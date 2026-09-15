import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit84Consumer
import QiushiOrbit13FP
import QiushiWcOrbit16Dispatch
import QiushiFlattenSeeds

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc84_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc84_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc84s0_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc84s0_contain :
    (o84SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 273) (codeMat 140) orbit13W := by
  change spanCodes [258, 128, 80, 32, 10, 4, 1] ≤ actionW (codeMat 273) (codeMat 140) orbit13W
  apply step109wc84_spanCodes_le_of_gens [258, 128, 80, 32, 10, 4, 1]
    (actionW (codeMat 273) (codeMat 140) orbit13W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 68 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 68) = codeMat 258 := by
      unfold actionA
      rw [step109wc84s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 68 * (codeMat 98 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 256 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 256) = codeMat 128 := by
      unfold actionA
      rw [step109wc84s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 256 * (codeMat 98 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 160 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 160) = codeMat 80 := by
      unfold actionA
      rw [step109wc84s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 160 * (codeMat 98 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc84s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 20 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 20 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 20) = codeMat 10 := by
      unfold actionA
      rw [step109wc84s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 20 * (codeMat 98 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 1) = codeMat 4 := by
      unfold actionA
      rw [step109wc84s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc84s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact

theorem step109wc84s0Dispatch :
    QuotientRankAtLeast (o84SourceU_wc ⟨0, by omega⟩) 12 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 140) orbit13W) 12 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 140) hP hQ orbit13W 12
      orbit13_lb12
  exact quotientRankAtLeast_mono step109wc84s0_contain hAct


private theorem step109wc84s1_QtInv :
    (codeMat 395 : Mat3).transpose⁻¹ = (codeMat 474 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 395 : Mat3).transpose * (codeMat 474 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc84s1_contain :
    (o84SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 169) (codeMat 395) o16W_wc := by
  change spanCodes [258, 128, 82, 32, 10, 6, 1] ≤ actionW (codeMat 169) (codeMat 395) o16W_wc
  apply step109wc84_spanCodes_le_of_gens [258, 128, 82, 32, 10, 6, 1]
    (actionW (codeMat 169) (codeMat 395) o16W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 33 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 33 (by decide)
    have hact : actionA (codeMat 169) (codeMat 395) (codeMat 33) = codeMat 258 := by
      unfold actionA
      rw [step109wc84s1_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 33 * (codeMat 474 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 45 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 45 (by decide)
    have hact : actionA (codeMat 169) (codeMat 395) (codeMat 45) = codeMat 128 := by
      unfold actionA
      rw [step109wc84s1_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 45 * (codeMat 474 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 350 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 350 (by decide)
    have hact : actionA (codeMat 169) (codeMat 395) (codeMat 350) = codeMat 82 := by
      unfold actionA
      rw [step109wc84s1_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 350 * (codeMat 474 : Mat3).transpose = codeMat 82
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 169) (codeMat 395) (codeMat 256) = codeMat 32 := by
      unfold actionA
      rw [step109wc84s1_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 256 * (codeMat 474 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 197 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 197 (by decide)
    have hact : actionA (codeMat 169) (codeMat 395) (codeMat 197) = codeMat 10 := by
      unfold actionA
      rw [step109wc84s1_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 197 * (codeMat 474 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 395) (codeMat 1) = codeMat 6 := by
      unfold actionA
      rw [step109wc84s1_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * (codeMat 474 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 3 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 169) (codeMat 395) (codeMat 3) = codeMat 1 := by
      unfold actionA
      rw [step109wc84s1_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 3 * (codeMat 474 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact

theorem step109wc84s1Dispatch :
    QuotientRankAtLeast (o84SourceU_wc ⟨1, by omega⟩) 12 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 395 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 395) o16W_wc) 12 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 395) hP hQ o16W_wc 12
      step109_orbit16_lb12_wc
  exact quotientRankAtLeast_mono step109wc84s1_contain hAct


private theorem step109wc84s2_QtInv :
    (codeMat 98 : Mat3).transpose⁻¹ = (codeMat 140 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 98 : Mat3).transpose * (codeMat 140 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc84s2_contain :
    (o84SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 98) (codeMat 98) orbit13W := by
  change spanCodes [258, 128, 68, 32, 16, 10, 1] ≤ actionW (codeMat 98) (codeMat 98) orbit13W
  apply step109wc84_spanCodes_le_of_gens [258, 128, 68, 32, 16, 10, 1]
    (actionW (codeMat 98) (codeMat 98) orbit13W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 80 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 80 (by decide)
    have hact : actionA (codeMat 98) (codeMat 98) (codeMat 80) = codeMat 258 := by
      unfold actionA
      rw [step109wc84s2_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 80 * (codeMat 140 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 8 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 98) (codeMat 98) (codeMat 8) = codeMat 128 := by
      unfold actionA
      rw [step109wc84s2_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 8 * (codeMat 140 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 160 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 98) (codeMat 98) (codeMat 160) = codeMat 68 := by
      unfold actionA
      rw [step109wc84s2_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 160 * (codeMat 140 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 98) (codeMat 98) (codeMat 2) = codeMat 32 := by
      unfold actionA
      rw [step109wc84s2_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 2 * (codeMat 140 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 98) (codeMat 98) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step109wc84s2_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 1 * (codeMat 140 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 68 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 98) (codeMat 98) (codeMat 68) = codeMat 10 := by
      unfold actionA
      rw [step109wc84s2_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 68 * (codeMat 140 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 98) (codeMat 98) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc84s2_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 256 * (codeMat 140 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact

theorem step109wc84s2Dispatch :
    QuotientRankAtLeast (o84SourceU_wc ⟨2, by omega⟩) 12 := by
  have hP : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 98) (codeMat 98) orbit13W) 12 :=
    @quotientRankAtLeast_action (codeMat 98) (codeMat 98) hP hQ orbit13W 12
      orbit13_lb12
  exact quotientRankAtLeast_mono step109wc84s2_contain hAct


private theorem step109wc84s3_QtInv :
    (codeMat 205 : Mat3).transpose⁻¹ = (codeMat 242 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 205 : Mat3).transpose * (codeMat 242 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc84s3_contain :
    (o84SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 226) (codeMat 205) o16W_wc := by
  change spanCodes [258, 128, 70, 32, 18, 10, 1] ≤ actionW (codeMat 226) (codeMat 205) o16W_wc
  apply step109wc84_spanCodes_le_of_gens [258, 128, 70, 32, 18, 10, 1]
    (actionW (codeMat 226) (codeMat 205) o16W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 268 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 268 (by decide)
    have hact : actionA (codeMat 226) (codeMat 205) (codeMat 268) = codeMat 258 := by
      unfold actionA
      rw [step109wc84s3_QtInv]
      show (codeMat 226 : Mat3).transpose * codeMat 268 * (codeMat 242 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 32 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 226) (codeMat 205) (codeMat 32) = codeMat 128 := by
      unfold actionA
      rw [step109wc84s3_QtInv]
      show (codeMat 226 : Mat3).transpose * codeMat 32 * (codeMat 242 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 381 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 381 (by decide)
    have hact : actionA (codeMat 226) (codeMat 205) (codeMat 381) = codeMat 70 := by
      unfold actionA
      rw [step109wc84s3_QtInv]
      show (codeMat 226 : Mat3).transpose * codeMat 381 * (codeMat 242 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 226) (codeMat 205) (codeMat 1) = codeMat 32 := by
      unfold actionA
      rw [step109wc84s3_QtInv]
      show (codeMat 226 : Mat3).transpose * codeMat 1 * (codeMat 242 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 256 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 226) (codeMat 205) (codeMat 256) = codeMat 18 := by
      unfold actionA
      rw [step109wc84s3_QtInv]
      show (codeMat 226 : Mat3).transpose * codeMat 256 * (codeMat 242 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 259 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 259 (by decide)
    have hact : actionA (codeMat 226) (codeMat 205) (codeMat 259) = codeMat 10 := by
      unfold actionA
      rw [step109wc84s3_QtInv]
      show (codeMat 226 : Mat3).transpose * codeMat 259 * (codeMat 242 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 455 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 455 (by decide)
    have hact : actionA (codeMat 226) (codeMat 205) (codeMat 455) = codeMat 1 := by
      unfold actionA
      rw [step109wc84s3_QtInv]
      show (codeMat 226 : Mat3).transpose * codeMat 455 * (codeMat 242 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact

theorem step109wc84s3Dispatch :
    QuotientRankAtLeast (o84SourceU_wc ⟨3, by omega⟩) 12 := by
  have hP : Invertible (codeMat 226 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 205 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 226) (codeMat 205) o16W_wc) 12 :=
    @quotientRankAtLeast_action (codeMat 226) (codeMat 205) hP hQ o16W_wc 12
      step109_orbit16_lb12_wc
  exact quotientRankAtLeast_mono step109wc84s3_contain hAct


private theorem step109wc84s4_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc84s4_contain :
    (o84SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 140) (codeMat 273) orbit13W := by
  change spanCodes [258, 128, 64, 32, 20, 10, 1] ≤ actionW (codeMat 140) (codeMat 273) orbit13W
  apply step109wc84_spanCodes_le_of_gens [258, 128, 64, 32, 20, 10, 1]
    (actionW (codeMat 140) (codeMat 273) orbit13W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 20 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 20 (by decide)
    have hact : actionA (codeMat 140) (codeMat 273) (codeMat 20) = codeMat 258 := by
      unfold actionA
      rw [step109wc84s4_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 20 * (codeMat 273 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 140) (codeMat 273) (codeMat 2) = codeMat 128 := by
      unfold actionA
      rw [step109wc84s4_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 140) (codeMat 273) (codeMat 1) = codeMat 64 := by
      unfold actionA
      rw [step109wc84s4_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 140) (codeMat 273) (codeMat 256) = codeMat 32 := by
      unfold actionA
      rw [step109wc84s4_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 256 * (codeMat 273 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 160 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 140) (codeMat 273) (codeMat 160) = codeMat 20 := by
      unfold actionA
      rw [step109wc84s4_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 160 * (codeMat 273 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 80 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 80 (by decide)
    have hact : actionA (codeMat 140) (codeMat 273) (codeMat 80) = codeMat 10 := by
      unfold actionA
      rw [step109wc84s4_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 80 * (codeMat 273 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 140) (codeMat 273) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc84s4_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 8 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact

theorem step109wc84s4Dispatch :
    QuotientRankAtLeast (o84SourceU_wc ⟨4, by omega⟩) 12 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 273) orbit13W) 12 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 273) hP hQ orbit13W 12
      orbit13_lb12
  exact quotientRankAtLeast_mono step109wc84s4_contain hAct


private theorem step109wc84s5_QtInv :
    (codeMat 342 : Mat3).transpose⁻¹ = (codeMat 215 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 342 : Mat3).transpose * (codeMat 215 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc84s5_contain :
    (o84SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 116) (codeMat 342) o16W_wc := by
  change spanCodes [258, 128, 66, 32, 22, 10, 1] ≤ actionW (codeMat 116) (codeMat 342) o16W_wc
  apply step109wc84_spanCodes_le_of_gens [258, 128, 66, 32, 22, 10, 1]
    (actionW (codeMat 116) (codeMat 342) o16W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 197 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 197 (by decide)
    have hact : actionA (codeMat 116) (codeMat 342) (codeMat 197) = codeMat 258 := by
      unfold actionA
      rw [step109wc84s5_QtInv]
      show (codeMat 116 : Mat3).transpose * codeMat 197 * (codeMat 215 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 3 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 116) (codeMat 342) (codeMat 3) = codeMat 128 := by
      unfold actionA
      rw [step109wc84s5_QtInv]
      show (codeMat 116 : Mat3).transpose * codeMat 3 * (codeMat 215 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 196 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 196 (by decide)
    have hact : actionA (codeMat 116) (codeMat 342) (codeMat 196) = codeMat 66 := by
      unfold actionA
      rw [step109wc84s5_QtInv]
      show (codeMat 116 : Mat3).transpose * codeMat 196 * (codeMat 215 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 45 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 45 (by decide)
    have hact : actionA (codeMat 116) (codeMat 342) (codeMat 45) = codeMat 32 := by
      unfold actionA
      rw [step109wc84s5_QtInv]
      show (codeMat 116 : Mat3).transpose * codeMat 45 * (codeMat 215 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 411 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 411 (by decide)
    have hact : actionA (codeMat 116) (codeMat 342) (codeMat 411) = codeMat 22 := by
      unfold actionA
      rw [step109wc84s5_QtInv]
      show (codeMat 116 : Mat3).transpose * codeMat 411 * (codeMat 215 : Mat3).transpose = codeMat 22
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 228 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 228 (by decide)
    have hact : actionA (codeMat 116) (codeMat 342) (codeMat 228) = codeMat 10 := by
      unfold actionA
      rw [step109wc84s5_QtInv]
      show (codeMat 116 : Mat3).transpose * codeMat 228 * (codeMat 215 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 116) (codeMat 342) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc84s5_QtInv]
      show (codeMat 116 : Mat3).transpose * codeMat 256 * (codeMat 215 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact

theorem step109wc84s5Dispatch :
    QuotientRankAtLeast (o84SourceU_wc ⟨5, by omega⟩) 12 := by
  have hP : Invertible (codeMat 116 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 342 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 116) (codeMat 342) o16W_wc) 12 :=
    @quotientRankAtLeast_action (codeMat 116) (codeMat 342) hP hQ o16W_wc 12
      step109_orbit16_lb12_wc
  exact quotientRankAtLeast_mono step109wc84s5_contain hAct


private theorem step109wc84s6_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc84s6_contain :
    (o84SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 84) (codeMat 84) flatW_15 := by
  change spanCodes [256, 128, 84, 32, 8, 2, 1] ≤ actionW (codeMat 84) (codeMat 84) flatW_15
  apply step109wc84_spanCodes_le_of_gens [256, 128, 84, 32, 8, 2, 1]
    (actionW (codeMat 84) (codeMat 84) flatW_15)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 1 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step109wc84s6_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 84 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 2) = codeMat 128 := by
      unfold actionA
      rw [step109wc84s6_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 84 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 84 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 84 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 84) = codeMat 84 := by
      unfold actionA
      rw [step109wc84s6_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 84 * (codeMat 84 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc84s6_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 84 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 32 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 32) = codeMat 8 := by
      unfold actionA
      rw [step109wc84s6_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 32 * (codeMat 84 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 128) = codeMat 2 := by
      unfold actionA
      rw [step109wc84s6_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 84 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc84s6_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 84 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc84_codeMat_mem_actionW_of_witness hw hact

theorem step109wc84s6Dispatch :
    QuotientRankAtLeast (o84SourceU_wc ⟨6, by omega⟩) 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 84) flatW_15) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 84) hP hQ flatW_15 9
      flatSeed_15
  exact quotientRankAtLeast_mono step109wc84s6_contain hAct

theorem step109wc84_all_dispatch (i : Fin 7) :
    QuotientRankAtLeast (o84SourceU_wc i) (o84SourceLb_wc i) := by
  fin_cases i
  · exact step109wc84s0Dispatch
  · exact step109wc84s1Dispatch
  · exact step109wc84s2Dispatch
  · exact step109wc84s3Dispatch
  · exact step109wc84s4Dispatch
  · exact step109wc84s5Dispatch
  · exact step109wc84s6Dispatch

theorem step109_orbit84_lb14_wc : QuotientRankAtLeast o84W_wc 14 :=
  o84Lb14_wc step109wc84_all_dispatch

end QiushiMatmul
