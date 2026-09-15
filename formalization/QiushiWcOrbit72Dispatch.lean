import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit72Consumer
import QiushiStep81Qdim2Generated
import QiushiOrbit11FP
import QiushiFlattenSeeds

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc72_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc72_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc72s0_QtInv :
    (codeMat 282 : Mat3).transpose⁻¹ = (codeMat 267 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 282 : Mat3).transpose * (codeMat 267 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc72s0_contain :
    (o72SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 86) (codeMat 282) step81o17s4Wspan := by
  change spanCodes [258, 130, 68, 32, 20, 10, 1] ≤ actionW (codeMat 86) (codeMat 282) step81o17s4Wspan
  apply step109wc72_spanCodes_le_of_gens [258, 130, 68, 32, 20, 10, 1]
    (actionW (codeMat 86) (codeMat 282) step81o17s4Wspan)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 228 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 228 (by decide)
    have hact : actionA (codeMat 86) (codeMat 282) (codeMat 228) = codeMat 258 := by
      unfold actionA
      rw [step109wc72s0_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 228 * (codeMat 267 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc72_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 219 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 219 (by decide)
    have hact : actionA (codeMat 86) (codeMat 282) (codeMat 219) = codeMat 130 := by
      unfold actionA
      rw [step109wc72s0_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 219 * (codeMat 267 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc72_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 274 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 274 (by decide)
    have hact : actionA (codeMat 86) (codeMat 282) (codeMat 274) = codeMat 68 := by
      unfold actionA
      rw [step109wc72s0_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 274 * (codeMat 267 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc72_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 32 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 86) (codeMat 282) (codeMat 32) = codeMat 32 := by
      unfold actionA
      rw [step109wc72s0_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 32 * (codeMat 267 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc72_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 280 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 280 (by decide)
    have hact : actionA (codeMat 86) (codeMat 282) (codeMat 280) = codeMat 20 := by
      unfold actionA
      rw [step109wc72s0_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 280 * (codeMat 267 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc72_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 208 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 208 (by decide)
    have hact : actionA (codeMat 86) (codeMat 282) (codeMat 208) = codeMat 10 := by
      unfold actionA
      rw [step109wc72s0_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 208 * (codeMat 267 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc72_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 86) (codeMat 282) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc72s0_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 128 * (codeMat 267 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc72_codeMat_mem_actionW_of_witness hw hact

theorem step109wc72s0Dispatch :
    QuotientRankAtLeast (o72SourceU_wc ⟨0, by omega⟩) 14 := by
  have hP : Invertible (codeMat 86 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 282 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 86) (codeMat 282) step81o17s4Wspan) 14 :=
    @quotientRankAtLeast_action (codeMat 86) (codeMat 282) hP hQ step81o17s4Wspan 14
      step81o17s4Span_lb
  exact quotientRankAtLeast_mono step109wc72s0_contain hAct


private theorem step109wc72s1_QtInv :
    (codeMat 286 : Mat3).transpose⁻¹ = (codeMat 303 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 286 : Mat3).transpose * (codeMat 303 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc72s1_contain :
    (o72SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 92) (codeMat 286) step81o17s4Wspan := by
  change spanCodes [258, 132, 68, 32, 20, 10, 1] ≤ actionW (codeMat 92) (codeMat 286) step81o17s4Wspan
  apply step109wc72_spanCodes_le_of_gens [258, 132, 68, 32, 20, 10, 1]
    (actionW (codeMat 92) (codeMat 286) step81o17s4Wspan)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 197 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 197 (by decide)
    have hact : actionA (codeMat 92) (codeMat 286) (codeMat 197) = codeMat 258 := by
      unfold actionA
      rw [step109wc72s1_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 197 * (codeMat 303 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc72_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 323 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 323 (by decide)
    have hact : actionA (codeMat 92) (codeMat 286) (codeMat 323) = codeMat 132 := by
      unfold actionA
      rw [step109wc72s1_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 323 * (codeMat 303 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc72_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 322 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 322 (by decide)
    have hact : actionA (codeMat 92) (codeMat 286) (codeMat 322) = codeMat 68 := by
      unfold actionA
      rw [step109wc72s1_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 322 * (codeMat 303 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc72_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 360 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 360 (by decide)
    have hact : actionA (codeMat 92) (codeMat 286) (codeMat 360) = codeMat 32 := by
      unfold actionA
      rw [step109wc72s1_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 360 * (codeMat 303 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc72_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 408 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 408 (by decide)
    have hact : actionA (codeMat 92) (codeMat 286) (codeMat 408) = codeMat 20 := by
      unfold actionA
      rw [step109wc72s1_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 408 * (codeMat 303 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc72_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 80 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 80 (by decide)
    have hact : actionA (codeMat 92) (codeMat 286) (codeMat 80) = codeMat 10 := by
      unfold actionA
      rw [step109wc72s1_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 80 * (codeMat 303 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc72_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 92) (codeMat 286) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc72s1_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 128 * (codeMat 303 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc72_codeMat_mem_actionW_of_witness hw hact

theorem step109wc72s1Dispatch :
    QuotientRankAtLeast (o72SourceU_wc ⟨1, by omega⟩) 14 := by
  have hP : Invertible (codeMat 92 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 286 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 92) (codeMat 286) step81o17s4Wspan) 14 :=
    @quotientRankAtLeast_action (codeMat 92) (codeMat 286) hP hQ step81o17s4Wspan 14
      step81o17s4Span_lb
  exact quotientRankAtLeast_mono step109wc72s1_contain hAct


private theorem step109wc72s2_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc72s2_contain :
    (o72SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 266) (codeMat 161) orbit11W := by
  change spanCodes [256, 68, 32, 20, 8, 2, 1] ≤ actionW (codeMat 266) (codeMat 161) orbit11W
  apply step109wc72_spanCodes_le_of_gens [256, 68, 32, 20, 8, 2, 1]
    (actionW (codeMat 266) (codeMat 161) orbit11W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 128 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 128 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 128) = codeMat 256 := by
      unfold actionA
      rw [step109wc72s2_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 128 * (codeMat 161 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc72_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 80 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 80 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 80) = codeMat 68 := by
      unfold actionA
      rw [step109wc72s2_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 80 * (codeMat 161 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc72_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 2) = codeMat 32 := by
      unfold actionA
      rw [step109wc72s2_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 161 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc72_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 20 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 20 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 20) = codeMat 20 := by
      unfold actionA
      rw [step109wc72s2_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 20 * (codeMat 161 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc72_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 1) = codeMat 8 := by
      unfold actionA
      rw [step109wc72s2_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc72_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 32 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 32) = codeMat 2 := by
      unfold actionA
      rw [step109wc72s2_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 161 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc72_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc72s2_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc72_codeMat_mem_actionW_of_witness hw hact

theorem step109wc72s2Dispatch :
    QuotientRankAtLeast (o72SourceU_wc ⟨2, by omega⟩) 12 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 161) orbit11W) 12 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 161) hP hQ orbit11W 12
      orbit11_lb12
  exact quotientRankAtLeast_mono step109wc72s2_contain hAct


private theorem step109wc72s3_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc72s3_contain :
    (o72SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 273) (codeMat 140) orbit11W := by
  change spanCodes [258, 64, 32, 16, 10, 4, 1] ≤ actionW (codeMat 273) (codeMat 140) orbit11W
  apply step109wc72_spanCodes_le_of_gens [258, 64, 32, 16, 10, 4, 1]
    (actionW (codeMat 273) (codeMat 140) orbit11W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 68 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 68 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 68) = codeMat 258 := by
      unfold actionA
      rw [step109wc72s3_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 68 * (codeMat 98 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc72_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 128 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 128 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 128) = codeMat 64 := by
      unfold actionA
      rw [step109wc72s3_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 128 * (codeMat 98 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc72_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc72s3_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc72_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 32 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 32 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 32) = codeMat 16 := by
      unfold actionA
      rw [step109wc72s3_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 32 * (codeMat 98 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc72_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 20 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 20 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 20) = codeMat 10 := by
      unfold actionA
      rw [step109wc72s3_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 20 * (codeMat 98 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc72_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 1) = codeMat 4 := by
      unfold actionA
      rw [step109wc72s3_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc72_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc72s3_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc72_codeMat_mem_actionW_of_witness hw hact

theorem step109wc72s3Dispatch :
    QuotientRankAtLeast (o72SourceU_wc ⟨3, by omega⟩) 12 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 140) orbit11W) 12 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 140) hP hQ orbit11W 12
      orbit11_lb12
  exact quotientRankAtLeast_mono step109wc72s3_contain hAct


private theorem step109wc72s4_QtInv :
    (codeMat 241 : Mat3).transpose⁻¹ = (codeMat 489 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 241 : Mat3).transpose * (codeMat 489 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc72s4_contain :
    (o72SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 87) (codeMat 241) flatW_2 := by
  change spanCodes [258, 128, 66, 32, 18, 10, 6, 1] ≤ actionW (codeMat 87) (codeMat 241) flatW_2
  apply step109wc72_spanCodes_le_of_gens [258, 128, 66, 32, 18, 10, 6, 1]
    (actionW (codeMat 87) (codeMat 241) flatW_2)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 274 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 274 (by decide)
    have hact : actionA (codeMat 87) (codeMat 241) (codeMat 274) = codeMat 258 := by
      unfold actionA
      rw [step109wc72s4_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 274 * (codeMat 489 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc72_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 438 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 438 (by decide)
    have hact : actionA (codeMat 87) (codeMat 241) (codeMat 438) = codeMat 128 := by
      unfold actionA
      rw [step109wc72s4_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 438 * (codeMat 489 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc72_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 237 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 237 (by decide)
    have hact : actionA (codeMat 87) (codeMat 241) (codeMat 237) = codeMat 66 := by
      unfold actionA
      rw [step109wc72s4_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 237 * (codeMat 489 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc72_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 16 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 16 (by decide)
    have hact : actionA (codeMat 87) (codeMat 241) (codeMat 16) = codeMat 32 := by
      unfold actionA
      rw [step109wc72s4_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 16 * (codeMat 489 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc72_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 432 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 432 (by decide)
    have hact : actionA (codeMat 87) (codeMat 241) (codeMat 432) = codeMat 18 := by
      unfold actionA
      rw [step109wc72s4_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 432 * (codeMat 489 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc72_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 424 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 424 (by decide)
    have hact : actionA (codeMat 87) (codeMat 241) (codeMat 424) = codeMat 10 := by
      unfold actionA
      rw [step109wc72s4_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 424 * (codeMat 489 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc72_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 87) (codeMat 241) (codeMat 256) = codeMat 6 := by
      unfold actionA
      rw [step109wc72s4_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 256 * (codeMat 489 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc72_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 320 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 320 (by decide)
    have hact : actionA (codeMat 87) (codeMat 241) (codeMat 320) = codeMat 1 := by
      unfold actionA
      rw [step109wc72s4_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 320 * (codeMat 489 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc72_codeMat_mem_actionW_of_witness hw hact

theorem step109wc72s4Dispatch :
    QuotientRankAtLeast (o72SourceU_wc ⟨4, by omega⟩) 6 := by
  have hP : Invertible (codeMat 87 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 241 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 87) (codeMat 241) flatW_2) 6 :=
    @quotientRankAtLeast_action (codeMat 87) (codeMat 241) hP hQ flatW_2 6
      flatSeed_2
  exact quotientRankAtLeast_mono step109wc72s4_contain hAct

theorem step109wc72_all_dispatch (i : Fin 5) :
    QuotientRankAtLeast (o72SourceU_wc i) (o72SourceLb_wc i) := by
  fin_cases i
  · exact step109wc72s0Dispatch
  · exact step109wc72s1Dispatch
  · exact step109wc72s2Dispatch
  · exact step109wc72s3Dispatch
  · exact step109wc72s4Dispatch

theorem step109_orbit72_lb15_wc : QuotientRankAtLeast o72W_wc 15 :=
  o72Lb15_wc step109wc72_all_dispatch

end QiushiMatmul
