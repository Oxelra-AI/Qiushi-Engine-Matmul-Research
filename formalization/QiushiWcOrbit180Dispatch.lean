import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiWcOrbit180Consumer
import QiushiStep99Orbit82Dispatch
import QiushiWcOrbit45Dispatch
import QiushiOrbit14FP
import QiushiOrbit10FP
import QiushiFlattenSeeds

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc180_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc180_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc180s0_QtInv :
    (codeMat 395 : Mat3).transpose⁻¹ = (codeMat 474 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 395 : Mat3).transpose * (codeMat 474 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc180s0_contain :
    (o180SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 103) (codeMat 395) o82W := by
  change spanCodes [262, 144, 84, 32, 10, 1] ≤ actionW (codeMat 103) (codeMat 395) o82W
  apply step109wc180_spanCodes_le_of_gens [262, 144, 84, 32, 10, 1]
    (actionW (codeMat 103) (codeMat 395) o82W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 96 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 96 (by decide)
    have hact : actionA (codeMat 103) (codeMat 395) (codeMat 96) = codeMat 262 := by
      unfold actionA
      rw [step109wc180s0_QtInv]
      show (codeMat 103 : Mat3).transpose * codeMat 96 * (codeMat 474 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 325 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 325 (by decide)
    have hact : actionA (codeMat 103) (codeMat 395) (codeMat 325) = codeMat 144 := by
      unfold actionA
      rw [step109wc180s0_QtInv]
      show (codeMat 103 : Mat3).transpose * codeMat 325 * (codeMat 474 : Mat3).transpose = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 117 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 117 (by decide)
    have hact : actionA (codeMat 103) (codeMat 395) (codeMat 117) = codeMat 84 := by
      unfold actionA
      rw [step109wc180s0_QtInv]
      show (codeMat 103 : Mat3).transpose * codeMat 117 * (codeMat 474 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 292 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 292 (by decide)
    have hact : actionA (codeMat 103) (codeMat 395) (codeMat 292) = codeMat 32 := by
      unfold actionA
      rw [step109wc180s0_QtInv]
      show (codeMat 103 : Mat3).transpose * codeMat 292 * (codeMat 474 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 411 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 411 (by decide)
    have hact : actionA (codeMat 103) (codeMat 395) (codeMat 411) = codeMat 10 := by
      unfold actionA
      rw [step109wc180s0_QtInv]
      show (codeMat 103 : Mat3).transpose * codeMat 411 * (codeMat 474 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 192 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 192 (by decide)
    have hact : actionA (codeMat 103) (codeMat 395) (codeMat 192) = codeMat 1 := by
      unfold actionA
      rw [step109wc180s0_QtInv]
      show (codeMat 103 : Mat3).transpose * codeMat 192 * (codeMat 474 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact

theorem step109wc180s0Dispatch :
    QuotientRankAtLeast (o180SourceU_wc ⟨0, by omega⟩) 14 := by
  have hP : Invertible (codeMat 103 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 395 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 103) (codeMat 395) o82W) 14 :=
    @quotientRankAtLeast_action (codeMat 103) (codeMat 395) hP hQ o82W 14
      step99_orbit82_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc180s0_contain hAct


private theorem step109wc180s1_QtInv :
    (codeMat 86 : Mat3).transpose⁻¹ = (codeMat 212 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 86 : Mat3).transpose * (codeMat 212 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc180s1_contain :
    (o180SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 426) (codeMat 86) o82W := by
  change spanCodes [276, 144, 84, 32, 10, 1] ≤ actionW (codeMat 426) (codeMat 86) o82W
  apply step109wc180_spanCodes_le_of_gens [276, 144, 84, 32, 10, 1]
    (actionW (codeMat 426) (codeMat 86) o82W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 11 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 426) (codeMat 86) (codeMat 11) = codeMat 276 := by
      unfold actionA
      rw [step109wc180s1_QtInv]
      show (codeMat 426 : Mat3).transpose * codeMat 11 * (codeMat 212 : Mat3).transpose = codeMat 276
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 192 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 192 (by decide)
    have hact : actionA (codeMat 426) (codeMat 86) (codeMat 192) = codeMat 144 := by
      unfold actionA
      rw [step109wc180s1_QtInv]
      show (codeMat 426 : Mat3).transpose * codeMat 192 * (codeMat 212 : Mat3).transpose = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 334 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 334 (by decide)
    have hact : actionA (codeMat 426) (codeMat 86) (codeMat 334) = codeMat 84 := by
      unfold actionA
      rw [step109wc180s1_QtInv]
      show (codeMat 426 : Mat3).transpose * codeMat 334 * (codeMat 212 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 426) (codeMat 86) (codeMat 1) = codeMat 32 := by
      unfold actionA
      rw [step109wc180s1_QtInv]
      show (codeMat 426 : Mat3).transpose * codeMat 1 * (codeMat 212 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 223 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 223 (by decide)
    have hact : actionA (codeMat 426) (codeMat 86) (codeMat 223) = codeMat 10 := by
      unfold actionA
      rw [step109wc180s1_QtInv]
      show (codeMat 426 : Mat3).transpose * codeMat 223 * (codeMat 212 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 292 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 292 (by decide)
    have hact : actionA (codeMat 426) (codeMat 86) (codeMat 292) = codeMat 1 := by
      unfold actionA
      rw [step109wc180s1_QtInv]
      show (codeMat 426 : Mat3).transpose * codeMat 292 * (codeMat 212 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact

theorem step109wc180s1Dispatch :
    QuotientRankAtLeast (o180SourceU_wc ⟨1, by omega⟩) 14 := by
  have hP : Invertible (codeMat 426 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 86 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 426) (codeMat 86) o82W) 14 :=
    @quotientRankAtLeast_action (codeMat 426) (codeMat 86) hP hQ o82W 14
      step99_orbit82_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc180s1_contain hAct


private theorem step109wc180s2_QtInv :
    (codeMat 98 : Mat3).transpose⁻¹ = (codeMat 140 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 98 : Mat3).transpose * (codeMat 140 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc180s2_contain :
    (o180SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 98) (codeMat 98) o45W_wc := by
  change spanCodes [128, 68, 32, 16, 10, 1] ≤ actionW (codeMat 98) (codeMat 98) o45W_wc
  apply step109wc180_spanCodes_le_of_gens [128, 68, 32, 16, 10, 1]
    (actionW (codeMat 98) (codeMat 98) o45W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 8 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 98) (codeMat 98) (codeMat 8) = codeMat 128 := by
      unfold actionA
      rw [step109wc180s2_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 8 * (codeMat 140 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 160 (by decide)
    have hact : actionA (codeMat 98) (codeMat 98) (codeMat 160) = codeMat 68 := by
      unfold actionA
      rw [step109wc180s2_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 160 * (codeMat 140 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 98) (codeMat 98) (codeMat 2) = codeMat 32 := by
      unfold actionA
      rw [step109wc180s2_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 2 * (codeMat 140 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 98) (codeMat 98) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step109wc180s2_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 1 * (codeMat 140 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 68 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 68 (by decide)
    have hact : actionA (codeMat 98) (codeMat 98) (codeMat 68) = codeMat 10 := by
      unfold actionA
      rw [step109wc180s2_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 68 * (codeMat 140 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 256 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 98) (codeMat 98) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc180s2_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 256 * (codeMat 140 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact

theorem step109wc180s2Dispatch :
    QuotientRankAtLeast (o180SourceU_wc ⟨2, by omega⟩) 13 := by
  have hP : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 98) (codeMat 98) o45W_wc) 13 :=
    @quotientRankAtLeast_action (codeMat 98) (codeMat 98) hP hQ o45W_wc 13
      step109_orbit45_lb13_wc
  exact quotientRankAtLeast_mono step109wc180s2_contain hAct


private theorem step109wc180s3_QtInv :
    (codeMat 214 : Mat3).transpose⁻¹ = (codeMat 214 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 214 : Mat3).transpose * (codeMat 214 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc180s3_contain :
    (o180SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 85) (codeMat 214) orbit14W := by
  change spanCodes [258, 144, 82, 32, 10, 6, 1] ≤ actionW (codeMat 85) (codeMat 214) orbit14W
  apply step109wc180_spanCodes_le_of_gens [258, 144, 82, 32, 10, 6, 1]
    (actionW (codeMat 85) (codeMat 214) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 385 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 385 (by decide)
    have hact : actionA (codeMat 85) (codeMat 214) (codeMat 385) = codeMat 258 := by
      unfold actionA
      rw [step109wc180s3_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 385 * (codeMat 214 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 511 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 511 (by decide)
    have hact : actionA (codeMat 85) (codeMat 214) (codeMat 511) = codeMat 144 := by
      unfold actionA
      rw [step109wc180s3_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 511 * (codeMat 214 : Mat3).transpose = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 252 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 252 (by decide)
    have hact : actionA (codeMat 85) (codeMat 214) (codeMat 252) = codeMat 82 := by
      unfold actionA
      rw [step109wc180s3_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 252 * (codeMat 214 : Mat3).transpose = codeMat 82
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 85) (codeMat 214) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc180s3_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 8 * (codeMat 214 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 480 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 480 (by decide)
    have hact : actionA (codeMat 85) (codeMat 214) (codeMat 480) = codeMat 10 := by
      unfold actionA
      rw [step109wc180s3_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 480 * (codeMat 214 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 85) (codeMat 214) (codeMat 384) = codeMat 6 := by
      unfold actionA
      rw [step109wc180s3_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 384 * (codeMat 214 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 85) (codeMat 214) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc180s3_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 256 * (codeMat 214 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact

theorem step109wc180s3Dispatch :
    QuotientRankAtLeast (o180SourceU_wc ⟨3, by omega⟩) 12 := by
  have hP : Invertible (codeMat 85 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 214 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 85) (codeMat 214) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 85) (codeMat 214) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc180s3_contain hAct


private theorem step109wc180s4_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc180s4_contain :
    (o180SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 84) (codeMat 84) orbit10W := by
  change spanCodes [256, 128, 68, 32, 16, 10, 1] ≤ actionW (codeMat 84) (codeMat 84) orbit10W
  apply step109wc180_spanCodes_le_of_gens [256, 128, 68, 32, 16, 10, 1]
    (actionW (codeMat 84) (codeMat 84) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step109wc180s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 84 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 2) = codeMat 128 := by
      unfold actionA
      rw [step109wc180s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 84 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 68) = codeMat 68 := by
      unfold actionA
      rw [step109wc180s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 68 * (codeMat 84 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc180s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 84 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 16) = codeMat 16 := by
      unfold actionA
      rw [step109wc180s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 16 * (codeMat 84 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step109wc180s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 160 * (codeMat 84 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc180s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 84 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact

theorem step109wc180s4Dispatch :
    QuotientRankAtLeast (o180SourceU_wc ⟨4, by omega⟩) 12 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 84) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 84) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc180s4_contain hAct


private theorem step109wc180s5_QtInv :
    (codeMat 355 : Mat3).transpose⁻¹ = (codeMat 190 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 355 : Mat3).transpose * (codeMat 190 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc180s5_contain :
    (o180SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 157) (codeMat 355) orbit14W := by
  change spanCodes [258, 130, 70, 32, 18, 10, 1] ≤ actionW (codeMat 157) (codeMat 355) orbit14W
  apply step109wc180_spanCodes_le_of_gens [258, 130, 70, 32, 18, 10, 1]
    (actionW (codeMat 157) (codeMat 355) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 510 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 510 (by decide)
    have hact : actionA (codeMat 157) (codeMat 355) (codeMat 510) = codeMat 258 := by
      unfold actionA
      rw [step109wc180s5_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 510 * (codeMat 190 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 157) (codeMat 355) (codeMat 1) = codeMat 130 := by
      unfold actionA
      rw [step109wc180s5_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 1 * (codeMat 190 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 149 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 149 (by decide)
    have hact : actionA (codeMat 157) (codeMat 355) (codeMat 149) = codeMat 70 := by
      unfold actionA
      rw [step109wc180s5_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 149 * (codeMat 190 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 157) (codeMat 355) (codeMat 384) = codeMat 32 := by
      unfold actionA
      rw [step109wc180s5_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 384 * (codeMat 190 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 157) (codeMat 355) (codeMat 8) = codeMat 18 := by
      unfold actionA
      rw [step109wc180s5_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 8 * (codeMat 190 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 264 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 264 (by decide)
    have hact : actionA (codeMat 157) (codeMat 355) (codeMat 264) = codeMat 10 := by
      unfold actionA
      rw [step109wc180s5_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 264 * (codeMat 190 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 157) (codeMat 355) (codeMat 360) = codeMat 1 := by
      unfold actionA
      rw [step109wc180s5_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 360 * (codeMat 190 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact

theorem step109wc180s5Dispatch :
    QuotientRankAtLeast (o180SourceU_wc ⟨5, by omega⟩) 12 := by
  have hP : Invertible (codeMat 157 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 355 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 157) (codeMat 355) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 157) (codeMat 355) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc180s5_contain hAct


private theorem step109wc180s6_QtInv :
    (codeMat 99 : Mat3).transpose⁻¹ = (codeMat 172 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 99 : Mat3).transpose * (codeMat 172 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc180s6_contain :
    (o180SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 158) (codeMat 99) orbit14W := by
  change spanCodes [256, 130, 70, 32, 18, 10, 1] ≤ actionW (codeMat 158) (codeMat 99) orbit14W
  apply step109wc180_spanCodes_le_of_gens [256, 130, 70, 32, 18, 10, 1]
    (actionW (codeMat 158) (codeMat 99) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 130 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 130 (by decide)
    have hact : actionA (codeMat 158) (codeMat 99) (codeMat 130) = codeMat 256 := by
      unfold actionA
      rw [step109wc180s6_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 130 * (codeMat 172 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 9 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 9 (by decide)
    have hact : actionA (codeMat 158) (codeMat 99) (codeMat 9) = codeMat 130 := by
      unfold actionA
      rw [step109wc180s6_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 9 * (codeMat 172 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 413 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 413 (by decide)
    have hact : actionA (codeMat 158) (codeMat 99) (codeMat 413) = codeMat 70 := by
      unfold actionA
      rw [step109wc180s6_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 413 * (codeMat 172 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 158) (codeMat 99) (codeMat 128) = codeMat 32 := by
      unfold actionA
      rw [step109wc180s6_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 128 * (codeMat 172 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 158) (codeMat 99) (codeMat 8) = codeMat 18 := by
      unfold actionA
      rw [step109wc180s6_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 8 * (codeMat 172 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 264 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 264 (by decide)
    have hact : actionA (codeMat 158) (codeMat 99) (codeMat 264) = codeMat 10 := by
      unfold actionA
      rw [step109wc180s6_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 264 * (codeMat 172 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 158) (codeMat 99) (codeMat 360) = codeMat 1 := by
      unfold actionA
      rw [step109wc180s6_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 360 * (codeMat 172 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact

theorem step109wc180s6Dispatch :
    QuotientRankAtLeast (o180SourceU_wc ⟨6, by omega⟩) 12 := by
  have hP : Invertible (codeMat 158 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 99 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 158) (codeMat 99) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 158) (codeMat 99) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc180s6_contain hAct


private theorem step109wc180s7_QtInv :
    (codeMat 157 : Mat3).transpose⁻¹ = (codeMat 486 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 157 : Mat3).transpose * (codeMat 486 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc180s7_contain :
    (o180SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 401) (codeMat 157) orbit14W := by
  change spanCodes [274, 144, 80, 32, 10, 4, 1] ≤ actionW (codeMat 401) (codeMat 157) orbit14W
  apply step109wc180_spanCodes_le_of_gens [274, 144, 80, 32, 10, 4, 1]
    (actionW (codeMat 401) (codeMat 157) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 126 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 126 (by decide)
    have hact : actionA (codeMat 401) (codeMat 157) (codeMat 126) = codeMat 274 := by
      unfold actionA
      rw [step109wc180s7_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 126 * (codeMat 486 : Mat3).transpose = codeMat 274
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 401) (codeMat 157) (codeMat 384) = codeMat 144 := by
      unfold actionA
      rw [step109wc180s7_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 384 * (codeMat 486 : Mat3).transpose = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 232 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 232 (by decide)
    have hact : actionA (codeMat 401) (codeMat 157) (codeMat 232) = codeMat 80 := by
      unfold actionA
      rw [step109wc180s7_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 232 * (codeMat 486 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 401) (codeMat 157) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc180s7_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 8 * (codeMat 486 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 30 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 30 (by decide)
    have hact : actionA (codeMat 401) (codeMat 157) (codeMat 30) = codeMat 10 := by
      unfold actionA
      rw [step109wc180s7_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 30 * (codeMat 486 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 401) (codeMat 157) (codeMat 1) = codeMat 4 := by
      unfold actionA
      rw [step109wc180s7_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 1 * (codeMat 486 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 401) (codeMat 157) (codeMat 3) = codeMat 1 := by
      unfold actionA
      rw [step109wc180s7_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 3 * (codeMat 486 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact

theorem step109wc180s7Dispatch :
    QuotientRankAtLeast (o180SourceU_wc ⟨7, by omega⟩) 12 := by
  have hP : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 157 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 401) (codeMat 157) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 401) (codeMat 157) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc180s7_contain hAct

private def step109wc180s8SrcT : Submodule F2 Mat3 := spanCodes [256, 132, 64, 16, 8, 2, 1]

private theorem step109wc180s8SrcT_lb : QuotientRankAtLeast step109wc180s8SrcT 9 := by
  have ht := quotientRankAtLeast_transpose flatSeed_7
  have hle : step109wc180s8SrcT ≤ transposeW flatW_7 := by
    unfold step109wc180s8SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
    · subst h0
      show codeMat 256 ∈ Submodule.map transposeLinearMap flatW_7
      exact ⟨codeMat 256, spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 256 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 132 ∈ Submodule.map transposeLinearMap flatW_7
      exact ⟨codeMat 96, spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 96 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 64 ∈ Submodule.map transposeLinearMap flatW_7
      exact ⟨codeMat 4, spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 4 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 16 ∈ Submodule.map transposeLinearMap flatW_7
      exact ⟨codeMat 16, spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 16 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 8 ∈ Submodule.map transposeLinearMap flatW_7
      exact ⟨codeMat 2, spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 2 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h5
      show codeMat 2 ∈ Submodule.map transposeLinearMap flatW_7
      exact ⟨codeMat 8, spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 8 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h6
      show codeMat 1 ∈ Submodule.map transposeLinearMap flatW_7
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc180s8_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc180s8_contain :
    (o180SourceU_wc ⟨8, by omega⟩) ≤ actionW (codeMat 177) (codeMat 273) step109wc180s8SrcT := by
  change spanCodes [132, 64, 32, 20, 8, 2, 1] ≤ actionW (codeMat 177) (codeMat 273) step109wc180s8SrcT
  apply step109wc180_spanCodes_le_of_gens [132, 64, 32, 20, 8, 2, 1]
    (actionW (codeMat 177) (codeMat 273) step109wc180s8SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 148 ∈ step109wc180s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 16, 8, 2, 1] 148 (by decide)
    have hact : actionA (codeMat 177) (codeMat 273) (codeMat 148) = codeMat 132 := by
      unfold actionA
      rw [step109wc180s8_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 148 * (codeMat 273 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 72 ∈ step109wc180s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 16, 8, 2, 1] 72 (by decide)
    have hact : actionA (codeMat 177) (codeMat 273) (codeMat 72) = codeMat 64 := by
      unfold actionA
      rw [step109wc180s8_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 72 * (codeMat 273 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 256 ∈ step109wc180s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 16, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 177) (codeMat 273) (codeMat 256) = codeMat 32 := by
      unfold actionA
      rw [step109wc180s8_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 256 * (codeMat 273 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 132 ∈ step109wc180s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 16, 8, 2, 1] 132 (by decide)
    have hact : actionA (codeMat 177) (codeMat 273) (codeMat 132) = codeMat 20 := by
      unfold actionA
      rw [step109wc180s8_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 132 * (codeMat 273 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 64 ∈ step109wc180s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 16, 8, 2, 1] 64 (by decide)
    have hact : actionA (codeMat 177) (codeMat 273) (codeMat 64) = codeMat 8 := by
      unfold actionA
      rw [step109wc180s8_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 64 * (codeMat 273 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ step109wc180s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 16, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 177) (codeMat 273) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc180s8_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 1 ∈ step109wc180s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 16, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc180s8_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc180_codeMat_mem_actionW_of_witness hw hact

theorem step109wc180s8Dispatch :
    QuotientRankAtLeast (o180SourceU_wc ⟨8, by omega⟩) 9 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 273) step109wc180s8SrcT) 9 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 273) hP hQ step109wc180s8SrcT 9
      step109wc180s8SrcT_lb
  exact quotientRankAtLeast_mono step109wc180s8_contain hAct

theorem step109wc180_all_dispatch (i : Fin 9) :
    QuotientRankAtLeast (o180SourceU_wc i) (o180SourceLb_wc i) := by
  fin_cases i
  · exact step109wc180s0Dispatch
  · exact step109wc180s1Dispatch
  · exact step109wc180s2Dispatch
  · exact step109wc180s3Dispatch
  · exact step109wc180s4Dispatch
  · exact step109wc180s5Dispatch
  · exact step109wc180s6Dispatch
  · exact step109wc180s7Dispatch
  · exact step109wc180s8Dispatch

theorem step109_orbit180_lb15_wc : QuotientRankAtLeast o180W_wc 15 :=
  o180Lb15_wc step109wc180_all_dispatch

end QiushiMatmul
