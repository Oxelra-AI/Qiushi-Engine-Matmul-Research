import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit79Consumer
import QiushiOrbit14FP
import QiushiOrbit13FP
import QiushiWcOrbit16Dispatch
import QiushiFlattenSeeds

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc79_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc79_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc79s0_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = (codeMat 275 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * (codeMat 275 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc79s0_contain :
    (o79SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 273) (codeMat 275) orbit14W := by
  change spanCodes [256, 160, 96, 20, 8, 2, 1] ≤ actionW (codeMat 273) (codeMat 275) orbit14W
  apply step109wc79_spanCodes_le_of_gens [256, 160, 96, 20, 8, 2, 1]
    (actionW (codeMat 273) (codeMat 275) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 256) = codeMat 256 := by
      unfold actionA
      rw [step109wc79s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 256 * (codeMat 275 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 224 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 224 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 224) = codeMat 160 := by
      unfold actionA
      rw [step109wc79s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 224 * (codeMat 275 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 96) = codeMat 96 := by
      unfold actionA
      rw [step109wc79s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 96 * (codeMat 275 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 28 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 28 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 28) = codeMat 20 := by
      unfold actionA
      rw [step109wc79s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 28 * (codeMat 275 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step109wc79s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 275 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [step109wc79s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 3 * (codeMat 275 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc79s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 275 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact

theorem step109wc79s0Dispatch :
    QuotientRankAtLeast (o79SourceU_wc ⟨0, by omega⟩) 12 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 275) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 275) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc79s0_contain hAct


private theorem step109wc79s1_QtInv :
    (codeMat 482 : Mat3).transpose⁻¹ = (codeMat 143 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 482 : Mat3).transpose * (codeMat 143 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc79s1_contain :
    (o79SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 95) (codeMat 482) orbit14W := by
  change spanCodes [258, 160, 96, 16, 10, 4, 1] ≤ actionW (codeMat 95) (codeMat 482) orbit14W
  apply step109wc79_spanCodes_le_of_gens [258, 160, 96, 16, 10, 4, 1]
    (actionW (codeMat 95) (codeMat 482) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 374 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 374 (by decide)
    have hact : actionA (codeMat 95) (codeMat 482) (codeMat 374) = codeMat 258 := by
      unfold actionA
      rw [step109wc79s1_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 374 * (codeMat 143 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 413 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 413 (by decide)
    have hact : actionA (codeMat 95) (codeMat 482) (codeMat 413) = codeMat 160 := by
      unfold actionA
      rw [step109wc79s1_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 413 * (codeMat 143 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 404 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 404 (by decide)
    have hact : actionA (codeMat 95) (codeMat 482) (codeMat 404) = codeMat 96 := by
      unfold actionA
      rw [step109wc79s1_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 404 * (codeMat 143 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 95) (codeMat 482) (codeMat 360) = codeMat 16 := by
      unfold actionA
      rw [step109wc79s1_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 360 * (codeMat 143 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 95) (codeMat 482) (codeMat 96) = codeMat 10 := by
      unfold actionA
      rw [step109wc79s1_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 96 * (codeMat 143 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 95) (codeMat 482) (codeMat 384) = codeMat 4 := by
      unfold actionA
      rw [step109wc79s1_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 384 * (codeMat 143 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 95) (codeMat 482) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc79s1_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 256 * (codeMat 143 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact

theorem step109wc79s1Dispatch :
    QuotientRankAtLeast (o79SourceU_wc ⟨1, by omega⟩) 12 := by
  have hP : Invertible (codeMat 95 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 482 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 95) (codeMat 482) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 95) (codeMat 482) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc79s1_contain hAct


private theorem step109wc79s2_QtInv :
    (codeMat 486 : Mat3).transpose⁻¹ = (codeMat 157 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 486 : Mat3).transpose * (codeMat 157 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc79s2_contain :
    (o79SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 86) (codeMat 486) orbit14W := by
  change spanCodes [258, 160, 96, 18, 10, 6, 1] ≤ actionW (codeMat 86) (codeMat 486) orbit14W
  apply step109wc79_spanCodes_le_of_gens [258, 160, 96, 18, 10, 6, 1]
    (actionW (codeMat 86) (codeMat 486) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 383 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 383 (by decide)
    have hact : actionA (codeMat 86) (codeMat 486) (codeMat 383) = codeMat 258 := by
      unfold actionA
      rw [step109wc79s2_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 383 * (codeMat 157 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 21 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 21 (by decide)
    have hact : actionA (codeMat 86) (codeMat 486) (codeMat 21) = codeMat 160 := by
      unfold actionA
      rw [step109wc79s2_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 21 * (codeMat 157 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 28 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 28 (by decide)
    have hact : actionA (codeMat 86) (codeMat 486) (codeMat 28) = codeMat 96 := by
      unfold actionA
      rw [step109wc79s2_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 28 * (codeMat 157 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 86) (codeMat 486) (codeMat 360) = codeMat 18 := by
      unfold actionA
      rw [step109wc79s2_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 360 * (codeMat 157 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 352 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 352 (by decide)
    have hact : actionA (codeMat 86) (codeMat 486) (codeMat 352) = codeMat 10 := by
      unfold actionA
      rw [step109wc79s2_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 352 * (codeMat 157 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 86) (codeMat 486) (codeMat 128) = codeMat 6 := by
      unfold actionA
      rw [step109wc79s2_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 128 * (codeMat 157 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 86) (codeMat 486) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc79s2_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 256 * (codeMat 157 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact

theorem step109wc79s2Dispatch :
    QuotientRankAtLeast (o79SourceU_wc ⟨2, by omega⟩) 12 := by
  have hP : Invertible (codeMat 86 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 486 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 86) (codeMat 486) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 86) (codeMat 486) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc79s2_contain hAct


private theorem step109wc79s3_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc79s3_contain :
    (o79SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 140) (codeMat 273) orbit13W := by
  change spanCodes [258, 128, 64, 32, 20, 10, 1] ≤ actionW (codeMat 140) (codeMat 273) orbit13W
  apply step109wc79_spanCodes_le_of_gens [258, 128, 64, 32, 20, 10, 1]
    (actionW (codeMat 140) (codeMat 273) orbit13W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 20 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 20 (by decide)
    have hact : actionA (codeMat 140) (codeMat 273) (codeMat 20) = codeMat 258 := by
      unfold actionA
      rw [step109wc79s3_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 20 * (codeMat 273 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 140) (codeMat 273) (codeMat 2) = codeMat 128 := by
      unfold actionA
      rw [step109wc79s3_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 140) (codeMat 273) (codeMat 1) = codeMat 64 := by
      unfold actionA
      rw [step109wc79s3_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 140) (codeMat 273) (codeMat 256) = codeMat 32 := by
      unfold actionA
      rw [step109wc79s3_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 256 * (codeMat 273 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 160 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 140) (codeMat 273) (codeMat 160) = codeMat 20 := by
      unfold actionA
      rw [step109wc79s3_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 160 * (codeMat 273 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 80 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 80 (by decide)
    have hact : actionA (codeMat 140) (codeMat 273) (codeMat 80) = codeMat 10 := by
      unfold actionA
      rw [step109wc79s3_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 80 * (codeMat 273 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 140) (codeMat 273) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc79s3_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 8 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact

theorem step109wc79s3Dispatch :
    QuotientRankAtLeast (o79SourceU_wc ⟨3, by omega⟩) 12 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 273) orbit13W) 12 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 273) hP hQ orbit13W 12
      orbit13_lb12
  exact quotientRankAtLeast_mono step109wc79s3_contain hAct


private theorem step109wc79s4_QtInv :
    (codeMat 334 : Mat3).transpose⁻¹ = (codeMat 442 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 334 : Mat3).transpose * (codeMat 442 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc79s4_contain :
    (o79SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 174) (codeMat 334) o16W_wc := by
  change spanCodes [258, 132, 68, 36, 20, 10, 1] ≤ actionW (codeMat 174) (codeMat 334) o16W_wc
  apply step109wc79_spanCodes_le_of_gens [258, 132, 68, 36, 20, 10, 1]
    (actionW (codeMat 174) (codeMat 334) o16W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 268 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 268 (by decide)
    have hact : actionA (codeMat 174) (codeMat 334) (codeMat 268) = codeMat 258 := by
      unfold actionA
      rw [step109wc79s4_QtInv]
      show (codeMat 174 : Mat3).transpose * codeMat 268 * (codeMat 442 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 300 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 300 (by decide)
    have hact : actionA (codeMat 174) (codeMat 334) (codeMat 300) = codeMat 132 := by
      unfold actionA
      rw [step109wc79s4_QtInv]
      show (codeMat 174 : Mat3).transpose * codeMat 300 * (codeMat 442 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 235 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 235 (by decide)
    have hact : actionA (codeMat 174) (codeMat 334) (codeMat 235) = codeMat 68 := by
      unfold actionA
      rw [step109wc79s4_QtInv]
      show (codeMat 174 : Mat3).transpose * codeMat 235 * (codeMat 442 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 45 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 45 (by decide)
    have hact : actionA (codeMat 174) (codeMat 334) (codeMat 45) = codeMat 36 := by
      unfold actionA
      rw [step109wc79s4_QtInv]
      show (codeMat 174 : Mat3).transpose * codeMat 45 * (codeMat 442 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 301 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 301 (by decide)
    have hact : actionA (codeMat 174) (codeMat 334) (codeMat 301) = codeMat 20 := by
      unfold actionA
      rw [step109wc79s4_QtInv]
      show (codeMat 174 : Mat3).transpose * codeMat 301 * (codeMat 442 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 457 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 457 (by decide)
    have hact : actionA (codeMat 174) (codeMat 334) (codeMat 457) = codeMat 10 := by
      unfold actionA
      rw [step109wc79s4_QtInv]
      show (codeMat 174 : Mat3).transpose * codeMat 457 * (codeMat 442 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 438 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 438 (by decide)
    have hact : actionA (codeMat 174) (codeMat 334) (codeMat 438) = codeMat 1 := by
      unfold actionA
      rw [step109wc79s4_QtInv]
      show (codeMat 174 : Mat3).transpose * codeMat 438 * (codeMat 442 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact

theorem step109wc79s4Dispatch :
    QuotientRankAtLeast (o79SourceU_wc ⟨4, by omega⟩) 12 := by
  have hP : Invertible (codeMat 174 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 334 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 174) (codeMat 334) o16W_wc) 12 :=
    @quotientRankAtLeast_action (codeMat 174) (codeMat 334) hP hQ o16W_wc 12
      step109_orbit16_lb12_wc
  exact quotientRankAtLeast_mono step109wc79s4_contain hAct


private theorem step109wc79s5_QtInv :
    (codeMat 106 : Mat3).transpose⁻¹ = (codeMat 396 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 106 : Mat3).transpose * (codeMat 396 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc79s5_contain :
    (o79SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 239) (codeMat 106) o16W_wc := by
  change spanCodes [258, 134, 70, 38, 20, 10, 1] ≤ actionW (codeMat 239) (codeMat 106) o16W_wc
  apply step109wc79_spanCodes_le_of_gens [258, 134, 70, 38, 20, 10, 1]
    (actionW (codeMat 239) (codeMat 106) o16W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 203 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 203 (by decide)
    have hact : actionA (codeMat 239) (codeMat 106) (codeMat 203) = codeMat 258 := by
      unfold actionA
      rw [step109wc79s5_QtInv]
      show (codeMat 239 : Mat3).transpose * codeMat 203 * (codeMat 396 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 154 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 154 (by decide)
    have hact : actionA (codeMat 239) (codeMat 106) (codeMat 154) = codeMat 134 := by
      unfold actionA
      rw [step109wc79s5_QtInv]
      show (codeMat 239 : Mat3).transpose * codeMat 154 * (codeMat 396 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 349 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 349 (by decide)
    have hact : actionA (codeMat 239) (codeMat 106) (codeMat 349) = codeMat 70 := by
      unfold actionA
      rw [step109wc79s5_QtInv]
      show (codeMat 239 : Mat3).transpose * codeMat 349 * (codeMat 396 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 201 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 201 (by decide)
    have hact : actionA (codeMat 239) (codeMat 106) (codeMat 201) = codeMat 38 := by
      unfold actionA
      rw [step109wc79s5_QtInv]
      show (codeMat 239 : Mat3).transpose * codeMat 201 * (codeMat 396 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 155 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 155 (by decide)
    have hact : actionA (codeMat 239) (codeMat 106) (codeMat 155) = codeMat 20 := by
      unfold actionA
      rw [step109wc79s5_QtInv]
      show (codeMat 239 : Mat3).transpose * codeMat 155 * (codeMat 396 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 127 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 127 (by decide)
    have hact : actionA (codeMat 239) (codeMat 106) (codeMat 127) = codeMat 10 := by
      unfold actionA
      rw [step109wc79s5_QtInv]
      show (codeMat 239 : Mat3).transpose * codeMat 127 * (codeMat 396 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 438 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 438 (by decide)
    have hact : actionA (codeMat 239) (codeMat 106) (codeMat 438) = codeMat 1 := by
      unfold actionA
      rw [step109wc79s5_QtInv]
      show (codeMat 239 : Mat3).transpose * codeMat 438 * (codeMat 396 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact

theorem step109wc79s5Dispatch :
    QuotientRankAtLeast (o79SourceU_wc ⟨5, by omega⟩) 12 := by
  have hP : Invertible (codeMat 239 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 106 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 239) (codeMat 106) o16W_wc) 12 :=
    @quotientRankAtLeast_action (codeMat 239) (codeMat 106) hP hQ o16W_wc 12
      step109_orbit16_lb12_wc
  exact quotientRankAtLeast_mono step109wc79s5_contain hAct


private theorem step109wc79s6_QtInv :
    (codeMat 407 : Mat3).transpose⁻¹ = (codeMat 405 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 407 : Mat3).transpose * (codeMat 405 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc79s6_contain :
    (o79SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 311) (codeMat 407) flatW_15 := by
  change spanCodes [258, 130, 66, 34, 20, 10, 1] ≤ actionW (codeMat 311) (codeMat 407) flatW_15
  apply step109wc79_spanCodes_le_of_gens [258, 130, 66, 34, 20, 10, 1]
    (actionW (codeMat 311) (codeMat 407) flatW_15)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 383 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 383 (by decide)
    have hact : actionA (codeMat 311) (codeMat 407) (codeMat 383) = codeMat 258 := by
      unfold actionA
      rw [step109wc79s6_QtInv]
      show (codeMat 311 : Mat3).transpose * codeMat 383 * (codeMat 405 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 511 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 511 (by decide)
    have hact : actionA (codeMat 311) (codeMat 407) (codeMat 511) = codeMat 130 := by
      unfold actionA
      rw [step109wc79s6_QtInv]
      show (codeMat 311 : Mat3).transpose * codeMat 511 * (codeMat 405 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 127 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 127 (by decide)
    have hact : actionA (codeMat 311) (codeMat 407) (codeMat 127) = codeMat 66 := by
      unfold actionA
      rw [step109wc79s6_QtInv]
      show (codeMat 311 : Mat3).transpose * codeMat 127 * (codeMat 405 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 343 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 343 (by decide)
    have hact : actionA (codeMat 311) (codeMat 407) (codeMat 343) = codeMat 34 := by
      unfold actionA
      rw [step109wc79s6_QtInv]
      show (codeMat 311 : Mat3).transpose * codeMat 343 * (codeMat 405 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 469 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 469 (by decide)
    have hact : actionA (codeMat 311) (codeMat 407) (codeMat 469) = codeMat 20 := by
      unfold actionA
      rw [step109wc79s6_QtInv]
      show (codeMat 311 : Mat3).transpose * codeMat 469 * (codeMat 405 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 119 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 119 (by decide)
    have hact : actionA (codeMat 311) (codeMat 407) (codeMat 119) = codeMat 10 := by
      unfold actionA
      rw [step109wc79s6_QtInv]
      show (codeMat 311 : Mat3).transpose * codeMat 119 * (codeMat 405 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 9 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 9 (by decide)
    have hact : actionA (codeMat 311) (codeMat 407) (codeMat 9) = codeMat 1 := by
      unfold actionA
      rw [step109wc79s6_QtInv]
      show (codeMat 311 : Mat3).transpose * codeMat 9 * (codeMat 405 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc79_codeMat_mem_actionW_of_witness hw hact

theorem step109wc79s6Dispatch :
    QuotientRankAtLeast (o79SourceU_wc ⟨6, by omega⟩) 9 := by
  have hP : Invertible (codeMat 311 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 407 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 311) (codeMat 407) flatW_15) 9 :=
    @quotientRankAtLeast_action (codeMat 311) (codeMat 407) hP hQ flatW_15 9
      flatSeed_15
  exact quotientRankAtLeast_mono step109wc79s6_contain hAct

theorem step109wc79_all_dispatch (i : Fin 7) :
    QuotientRankAtLeast (o79SourceU_wc i) (o79SourceLb_wc i) := by
  fin_cases i
  · exact step109wc79s0Dispatch
  · exact step109wc79s1Dispatch
  · exact step109wc79s2Dispatch
  · exact step109wc79s3Dispatch
  · exact step109wc79s4Dispatch
  · exact step109wc79s5Dispatch
  · exact step109wc79s6Dispatch

theorem step109_orbit79_lb14_wc : QuotientRankAtLeast o79W_wc 14 :=
  o79Lb14_wc step109wc79_all_dispatch

end QiushiMatmul
