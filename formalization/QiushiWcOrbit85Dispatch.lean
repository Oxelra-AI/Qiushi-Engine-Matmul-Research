import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit85Consumer
import QiushiStep81Qdim2Generated

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc85_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc85_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc85s0_QtInv :
    (codeMat 314 : Mat3).transpose⁻¹ = (codeMat 271 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 314 : Mat3).transpose * (codeMat 271 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc85s0_contain :
    (o85SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 86) (codeMat 314) step81o17s4Wspan := by
  change spanCodes [262, 130, 68, 34, 20, 10, 1] ≤ actionW (codeMat 86) (codeMat 314) step81o17s4Wspan
  apply step109wc85_spanCodes_le_of_gens [262, 130, 68, 34, 20, 10, 1]
    (actionW (codeMat 86) (codeMat 314) step81o17s4Wspan)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 374 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 374 (by decide)
    have hact : actionA (codeMat 86) (codeMat 314) (codeMat 374) = codeMat 262 := by
      unfold actionA
      rw [step109wc85s0_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 374 * (codeMat 271 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 219 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 219 (by decide)
    have hact : actionA (codeMat 86) (codeMat 314) (codeMat 219) = codeMat 130 := by
      unfold actionA
      rw [step109wc85s0_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 219 * (codeMat 271 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 402 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 402 (by decide)
    have hact : actionA (codeMat 86) (codeMat 314) (codeMat 402) = codeMat 68 := by
      unfold actionA
      rw [step109wc85s0_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 402 * (codeMat 271 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 240 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 240 (by decide)
    have hact : actionA (codeMat 86) (codeMat 314) (codeMat 240) = codeMat 34 := by
      unfold actionA
      rw [step109wc85s0_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 240 * (codeMat 271 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 408 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 408 (by decide)
    have hact : actionA (codeMat 86) (codeMat 314) (codeMat 408) = codeMat 20 := by
      unfold actionA
      rw [step109wc85s0_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 408 * (codeMat 271 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 208 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 208 (by decide)
    have hact : actionA (codeMat 86) (codeMat 314) (codeMat 208) = codeMat 10 := by
      unfold actionA
      rw [step109wc85s0_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 208 * (codeMat 271 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 86) (codeMat 314) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc85s0_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 128 * (codeMat 271 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact

theorem step109wc85s0Dispatch :
    QuotientRankAtLeast (o85SourceU_wc ⟨0, by omega⟩) 14 := by
  have hP : Invertible (codeMat 86 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 314 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 86) (codeMat 314) step81o17s4Wspan) 14 :=
    @quotientRankAtLeast_action (codeMat 86) (codeMat 314) hP hQ step81o17s4Wspan 14
      step81o17s4Span_lb
  exact quotientRankAtLeast_mono step109wc85s0_contain hAct


private theorem step109wc85s1_QtInv :
    (codeMat 116 : Mat3).transpose⁻¹ = (codeMat 92 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 116 : Mat3).transpose * (codeMat 92 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc85s1_contain :
    (o85SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 86) (codeMat 116) step81o17s4Wspan := by
  change spanCodes [260, 129, 68, 33, 20, 8, 2] ≤ actionW (codeMat 86) (codeMat 116) step81o17s4Wspan
  apply step109wc85_spanCodes_le_of_gens [260, 129, 68, 33, 20, 8, 2]
    (actionW (codeMat 86) (codeMat 116) step81o17s4Wspan)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 219 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 219 (by decide)
    have hact : actionA (codeMat 86) (codeMat 116) (codeMat 219) = codeMat 260 := by
      unfold actionA
      rw [step109wc85s1_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 219 * (codeMat 92 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 274 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 274 (by decide)
    have hact : actionA (codeMat 86) (codeMat 116) (codeMat 274) = codeMat 129 := by
      unfold actionA
      rw [step109wc85s1_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 274 * (codeMat 92 : Mat3).transpose = codeMat 129
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 228 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 228 (by decide)
    have hact : actionA (codeMat 86) (codeMat 116) (codeMat 228) = codeMat 68 := by
      unfold actionA
      rw [step109wc85s1_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 228 * (codeMat 92 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 280 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 280 (by decide)
    have hact : actionA (codeMat 86) (codeMat 116) (codeMat 280) = codeMat 33 := by
      unfold actionA
      rw [step109wc85s1_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 280 * (codeMat 92 : Mat3).transpose = codeMat 33
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 208 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 208 (by decide)
    have hact : actionA (codeMat 86) (codeMat 116) (codeMat 208) = codeMat 20 := by
      unfold actionA
      rw [step109wc85s1_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 208 * (codeMat 92 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 86) (codeMat 116) (codeMat 32) = codeMat 8 := by
      unfold actionA
      rw [step109wc85s1_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 32 * (codeMat 92 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 86) (codeMat 116) (codeMat 128) = codeMat 2 := by
      unfold actionA
      rw [step109wc85s1_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 128 * (codeMat 92 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact

theorem step109wc85s1Dispatch :
    QuotientRankAtLeast (o85SourceU_wc ⟨1, by omega⟩) 14 := by
  have hP : Invertible (codeMat 86 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 116 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 86) (codeMat 116) step81o17s4Wspan) 14 :=
    @quotientRankAtLeast_action (codeMat 86) (codeMat 116) hP hQ step81o17s4Wspan 14
      step81o17s4Span_lb
  exact quotientRankAtLeast_mono step109wc85s1_contain hAct


private theorem step109wc85s2_QtInv :
    (codeMat 467 : Mat3).transpose⁻¹ = (codeMat 339 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 467 : Mat3).transpose * (codeMat 339 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc85s2_contain :
    (o85SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 86) (codeMat 467) step81o17s4Wspan := by
  change spanCodes [261, 128, 68, 32, 20, 9, 3] ≤ actionW (codeMat 86) (codeMat 467) step81o17s4Wspan
  apply step109wc85_spanCodes_le_of_gens [261, 128, 68, 32, 20, 9, 3]
    (actionW (codeMat 86) (codeMat 467) step81o17s4Wspan)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 100 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 100 (by decide)
    have hact : actionA (codeMat 86) (codeMat 467) (codeMat 100) = codeMat 261 := by
      unfold actionA
      rw [step109wc85s2_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 100 * (codeMat 339 : Mat3).transpose = codeMat 261
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 63 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 63 (by decide)
    have hact : actionA (codeMat 86) (codeMat 467) (codeMat 63) = codeMat 128 := by
      unfold actionA
      rw [step109wc85s2_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 63 * (codeMat 339 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 301 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 301 (by decide)
    have hact : actionA (codeMat 86) (codeMat 467) (codeMat 301) = codeMat 68 := by
      unfold actionA
      rw [step109wc85s2_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 301 * (codeMat 339 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 32 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 86) (codeMat 467) (codeMat 32) = codeMat 32 := by
      unfold actionA
      rw [step109wc85s2_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 32 * (codeMat 339 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 312 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 312 (by decide)
    have hact : actionA (codeMat 86) (codeMat 467) (codeMat 312) = codeMat 20 := by
      unfold actionA
      rw [step109wc85s2_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 312 * (codeMat 339 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 360 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 360 (by decide)
    have hact : actionA (codeMat 86) (codeMat 467) (codeMat 360) = codeMat 9 := by
      unfold actionA
      rw [step109wc85s2_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 360 * (codeMat 339 : Mat3).transpose = codeMat 9
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 86) (codeMat 467) (codeMat 128) = codeMat 3 := by
      unfold actionA
      rw [step109wc85s2_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 128 * (codeMat 339 : Mat3).transpose = codeMat 3
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact

theorem step109wc85s2Dispatch :
    QuotientRankAtLeast (o85SourceU_wc ⟨2, by omega⟩) 14 := by
  have hP : Invertible (codeMat 86 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 467 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 86) (codeMat 467) step81o17s4Wspan) 14 :=
    @quotientRankAtLeast_action (codeMat 86) (codeMat 467) hP hQ step81o17s4Wspan 14
      step81o17s4Span_lb
  exact quotientRankAtLeast_mono step109wc85s2_contain hAct


private theorem step109wc85s3_QtInv :
    (codeMat 233 : Mat3).transpose⁻¹ = (codeMat 233 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 233 : Mat3).transpose * (codeMat 233 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc85s3_contain :
    (o85SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 86) (codeMat 233) step81o17s4Wspan := by
  change spanCodes [258, 131, 64, 35, 16, 10, 4] ≤ actionW (codeMat 86) (codeMat 233) step81o17s4Wspan
  apply step109wc85_spanCodes_le_of_gens [258, 131, 64, 35, 16, 10, 4]
    (actionW (codeMat 86) (codeMat 233) step81o17s4Wspan)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 274 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 274 (by decide)
    have hact : actionA (codeMat 86) (codeMat 233) (codeMat 274) = codeMat 258 := by
      unfold actionA
      rw [step109wc85s3_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 274 * (codeMat 233 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 228 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 228 (by decide)
    have hact : actionA (codeMat 86) (codeMat 233) (codeMat 228) = codeMat 131 := by
      unfold actionA
      rw [step109wc85s3_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 228 * (codeMat 233 : Mat3).transpose = codeMat 131
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 63 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 63 (by decide)
    have hact : actionA (codeMat 86) (codeMat 233) (codeMat 63) = codeMat 64 := by
      unfold actionA
      rw [step109wc85s3_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 63 * (codeMat 233 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 208 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 208 (by decide)
    have hact : actionA (codeMat 86) (codeMat 233) (codeMat 208) = codeMat 35 := by
      unfold actionA
      rw [step109wc85s3_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 208 * (codeMat 233 : Mat3).transpose = codeMat 35
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 32 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 86) (codeMat 233) (codeMat 32) = codeMat 16 := by
      unfold actionA
      rw [step109wc85s3_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 32 * (codeMat 233 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 312 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 312 (by decide)
    have hact : actionA (codeMat 86) (codeMat 233) (codeMat 312) = codeMat 10 := by
      unfold actionA
      rw [step109wc85s3_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 312 * (codeMat 233 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 86) (codeMat 233) (codeMat 128) = codeMat 4 := by
      unfold actionA
      rw [step109wc85s3_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 128 * (codeMat 233 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact

theorem step109wc85s3Dispatch :
    QuotientRankAtLeast (o85SourceU_wc ⟨3, by omega⟩) 14 := by
  have hP : Invertible (codeMat 86 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 233 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 86) (codeMat 233) step81o17s4Wspan) 14 :=
    @quotientRankAtLeast_action (codeMat 86) (codeMat 233) hP hQ step81o17s4Wspan 14
      step81o17s4Span_lb
  exact quotientRankAtLeast_mono step109wc85s3_contain hAct


private theorem step109wc85s4_QtInv :
    (codeMat 157 : Mat3).transpose⁻¹ = (codeMat 486 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 157 : Mat3).transpose * (codeMat 486 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc85s4_contain :
    (o85SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 86) (codeMat 157) step81o17s4Wspan := by
  change spanCodes [259, 131, 65, 35, 17, 10, 5] ≤ actionW (codeMat 86) (codeMat 157) step81o17s4Wspan
  apply step109wc85_spanCodes_le_of_gens [259, 131, 65, 35, 17, 10, 5]
    (actionW (codeMat 86) (codeMat 157) step81o17s4Wspan)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 329 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 329 (by decide)
    have hact : actionA (codeMat 86) (codeMat 157) (codeMat 329) = codeMat 259 := by
      unfold actionA
      rw [step109wc85s4_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 329 * (codeMat 486 : Mat3).transpose = codeMat 259
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 374 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 374 (by decide)
    have hact : actionA (codeMat 86) (codeMat 157) (codeMat 374) = codeMat 131 := by
      unfold actionA
      rw [step109wc85s4_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 374 * (codeMat 486 : Mat3).transpose = codeMat 131
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 219 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 219 (by decide)
    have hact : actionA (codeMat 86) (codeMat 157) (codeMat 219) = codeMat 65 := by
      unfold actionA
      rw [step109wc85s4_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 219 * (codeMat 486 : Mat3).transpose = codeMat 65
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 328 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 328 (by decide)
    have hact : actionA (codeMat 86) (codeMat 157) (codeMat 328) = codeMat 35 := by
      unfold actionA
      rw [step109wc85s4_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 328 * (codeMat 486 : Mat3).transpose = codeMat 35
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 240 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 240 (by decide)
    have hact : actionA (codeMat 86) (codeMat 157) (codeMat 240) = codeMat 17 := by
      unfold actionA
      rw [step109wc85s4_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 240 * (codeMat 486 : Mat3).transpose = codeMat 17
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 408 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 408 (by decide)
    have hact : actionA (codeMat 86) (codeMat 157) (codeMat 408) = codeMat 10 := by
      unfold actionA
      rw [step109wc85s4_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 408 * (codeMat 486 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 86) (codeMat 157) (codeMat 128) = codeMat 5 := by
      unfold actionA
      rw [step109wc85s4_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 128 * (codeMat 486 : Mat3).transpose = codeMat 5
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact

theorem step109wc85s4Dispatch :
    QuotientRankAtLeast (o85SourceU_wc ⟨4, by omega⟩) 14 := by
  have hP : Invertible (codeMat 86 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 157 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 86) (codeMat 157) step81o17s4Wspan) 14 :=
    @quotientRankAtLeast_action (codeMat 86) (codeMat 157) hP hQ step81o17s4Wspan 14
      step81o17s4Span_lb
  exact quotientRankAtLeast_mono step109wc85s4_contain hAct


private theorem step109wc85s5_QtInv :
    (codeMat 423 : Mat3).transpose⁻¹ = (codeMat 181 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 423 : Mat3).transpose * (codeMat 181 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc85s5_contain :
    (o85SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 86) (codeMat 423) step81o17s4Wspan := by
  change spanCodes [256, 131, 66, 35, 18, 10, 6] ≤ actionW (codeMat 86) (codeMat 423) step81o17s4Wspan
  apply step109wc85_spanCodes_le_of_gens [256, 131, 66, 35, 18, 10, 6]
    (actionW (codeMat 86) (codeMat 423) step81o17s4Wspan)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 63 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 63 (by decide)
    have hact : actionA (codeMat 86) (codeMat 423) (codeMat 63) = codeMat 256 := by
      unfold actionA
      rw [step109wc85s5_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 63 * (codeMat 181 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 301 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 301 (by decide)
    have hact : actionA (codeMat 86) (codeMat 423) (codeMat 301) = codeMat 131 := by
      unfold actionA
      rw [step109wc85s5_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 301 * (codeMat 181 : Mat3).transpose = codeMat 131
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 329 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 329 (by decide)
    have hact : actionA (codeMat 86) (codeMat 423) (codeMat 329) = codeMat 66 := by
      unfold actionA
      rw [step109wc85s5_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 329 * (codeMat 181 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 312 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 312 (by decide)
    have hact : actionA (codeMat 86) (codeMat 423) (codeMat 312) = codeMat 35 := by
      unfold actionA
      rw [step109wc85s5_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 312 * (codeMat 181 : Mat3).transpose = codeMat 35
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 360 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 360 (by decide)
    have hact : actionA (codeMat 86) (codeMat 423) (codeMat 360) = codeMat 18 := by
      unfold actionA
      rw [step109wc85s5_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 360 * (codeMat 181 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 328 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 328 (by decide)
    have hact : actionA (codeMat 86) (codeMat 423) (codeMat 328) = codeMat 10 := by
      unfold actionA
      rw [step109wc85s5_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 328 * (codeMat 181 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 86) (codeMat 423) (codeMat 128) = codeMat 6 := by
      unfold actionA
      rw [step109wc85s5_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 128 * (codeMat 181 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact

theorem step109wc85s5Dispatch :
    QuotientRankAtLeast (o85SourceU_wc ⟨5, by omega⟩) 14 := by
  have hP : Invertible (codeMat 86 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 423 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 86) (codeMat 423) step81o17s4Wspan) 14 :=
    @quotientRankAtLeast_action (codeMat 86) (codeMat 423) hP hQ step81o17s4Wspan 14
      step81o17s4Span_lb
  exact quotientRankAtLeast_mono step109wc85s5_contain hAct


private theorem step109wc85s6_QtInv :
    (codeMat 334 : Mat3).transpose⁻¹ = (codeMat 442 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 334 : Mat3).transpose * (codeMat 442 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc85s6_contain :
    (o85SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 86) (codeMat 334) step81o17s4Wspan := by
  change spanCodes [257, 131, 67, 35, 19, 10, 7] ≤ actionW (codeMat 86) (codeMat 334) step81o17s4Wspan
  apply step109wc85_spanCodes_le_of_gens [257, 131, 67, 35, 19, 10, 7]
    (actionW (codeMat 86) (codeMat 334) step81o17s4Wspan)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 429 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 429 (by decide)
    have hact : actionA (codeMat 86) (codeMat 334) (codeMat 429) = codeMat 257 := by
      unfold actionA
      rw [step109wc85s6_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 429 * (codeMat 442 : Mat3).transpose = codeMat 257
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 457 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 457 (by decide)
    have hact : actionA (codeMat 86) (codeMat 334) (codeMat 457) = codeMat 131 := by
      unfold actionA
      rw [step109wc85s6_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 457 * (codeMat 442 : Mat3).transpose = codeMat 131
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 502 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 502 (by decide)
    have hact : actionA (codeMat 86) (codeMat 334) (codeMat 502) = codeMat 67 := by
      unfold actionA
      rw [step109wc85s6_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 502 * (codeMat 442 : Mat3).transpose = codeMat 67
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 488 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 488 (by decide)
    have hact : actionA (codeMat 86) (codeMat 334) (codeMat 488) = codeMat 35 := by
      unfold actionA
      rw [step109wc85s6_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 488 * (codeMat 442 : Mat3).transpose = codeMat 35
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 456 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 456 (by decide)
    have hact : actionA (codeMat 86) (codeMat 334) (codeMat 456) = codeMat 19 := by
      unfold actionA
      rw [step109wc85s6_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 456 * (codeMat 442 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 112 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 112 (by decide)
    have hact : actionA (codeMat 86) (codeMat 334) (codeMat 112) = codeMat 10 := by
      unfold actionA
      rw [step109wc85s6_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 112 * (codeMat 442 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 86) (codeMat 334) (codeMat 128) = codeMat 7 := by
      unfold actionA
      rw [step109wc85s6_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 128 * (codeMat 442 : Mat3).transpose = codeMat 7
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc85_codeMat_mem_actionW_of_witness hw hact

theorem step109wc85s6Dispatch :
    QuotientRankAtLeast (o85SourceU_wc ⟨6, by omega⟩) 14 := by
  have hP : Invertible (codeMat 86 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 334 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 86) (codeMat 334) step81o17s4Wspan) 14 :=
    @quotientRankAtLeast_action (codeMat 86) (codeMat 334) hP hQ step81o17s4Wspan 14
      step81o17s4Span_lb
  exact quotientRankAtLeast_mono step109wc85s6_contain hAct

theorem step109wc85_all_dispatch (i : Fin 7) :
    QuotientRankAtLeast (o85SourceU_wc i) (o85SourceLb_wc i) := by
  fin_cases i
  · exact step109wc85s0Dispatch
  · exact step109wc85s1Dispatch
  · exact step109wc85s2Dispatch
  · exact step109wc85s3Dispatch
  · exact step109wc85s4Dispatch
  · exact step109wc85s5Dispatch
  · exact step109wc85s6Dispatch

theorem step109_orbit85_lb17_wc : QuotientRankAtLeast o85W_wc 17 :=
  o85Lb17_wc step109wc85_all_dispatch

end QiushiMatmul
