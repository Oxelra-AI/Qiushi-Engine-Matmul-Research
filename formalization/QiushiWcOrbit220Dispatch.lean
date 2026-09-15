import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit220Consumer
import QiushiStep99Orbit82Dispatch
import QiushiMonoOrbit43From14
import QiushiOrbit14FP
import QiushiOrbit10FP
import QiushiFlattenSeeds

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc220_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc220_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc220s0_QtInv :
    (codeMat 167 : Mat3).transpose⁻¹ = (codeMat 167 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 167 : Mat3).transpose * (codeMat 167 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc220s0_contain :
    (o220SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 241) (codeMat 167) o82W := by
  change spanCodes [258, 140, 76, 36, 16, 1] ≤ actionW (codeMat 241) (codeMat 167) o82W
  apply step109wc220_spanCodes_le_of_gens [258, 140, 76, 36, 16, 1]
    (actionW (codeMat 241) (codeMat 167) o82W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 222 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 222 (by decide)
    have hact : actionA (codeMat 241) (codeMat 167) (codeMat 222) = codeMat 258 := by
      unfold actionA
      rw [step109wc220s0_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 222 * (codeMat 167 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 303 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 303 (by decide)
    have hact : actionA (codeMat 241) (codeMat 167) (codeMat 303) = codeMat 140 := by
      unfold actionA
      rw [step109wc220s0_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 303 * (codeMat 167 : Mat3).transpose = codeMat 140
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 11 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 241) (codeMat 167) (codeMat 11) = codeMat 76 := by
      unfold actionA
      rw [step109wc220s0_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 11 * (codeMat 167 : Mat3).transpose = codeMat 76
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 192 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 192 (by decide)
    have hact : actionA (codeMat 241) (codeMat 167) (codeMat 192) = codeMat 36 := by
      unfold actionA
      rw [step109wc220s0_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 192 * (codeMat 167 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 325 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 325 (by decide)
    have hact : actionA (codeMat 241) (codeMat 167) (codeMat 325) = codeMat 16 := by
      unfold actionA
      rw [step109wc220s0_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 325 * (codeMat 167 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 241) (codeMat 167) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc220s0_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 1 * (codeMat 167 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact

theorem step109wc220s0Dispatch :
    QuotientRankAtLeast (o220SourceU_wc ⟨0, by omega⟩) 14 := by
  have hP : Invertible (codeMat 241 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 167 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 241) (codeMat 167) o82W) 14 :=
    @quotientRankAtLeast_action (codeMat 241) (codeMat 167) hP hQ o82W 14
      step99_orbit82_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc220s0_contain hAct


private theorem step109wc220s1_QtInv :
    (codeMat 279 : Mat3).transpose⁻¹ = (codeMat 279 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 279 : Mat3).transpose * (codeMat 279 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc220s1_contain :
    (o220SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 410) (codeMat 279) o43W_mono := by
  change spanCodes [326, 192, 36, 16, 8, 1] ≤ actionW (codeMat 410) (codeMat 279) o43W_mono
  apply step109wc220_spanCodes_le_of_gens [326, 192, 36, 16, 8, 1]
    (actionW (codeMat 410) (codeMat 279) o43W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 306 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 306 (by decide)
    have hact : actionA (codeMat 410) (codeMat 279) (codeMat 306) = codeMat 326 := by
      unfold actionA
      rw [step109wc220s1_QtInv]
      show (codeMat 410 : Mat3).transpose * codeMat 306 * (codeMat 279 : Mat3).transpose = codeMat 326
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 130 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 130 (by decide)
    have hact : actionA (codeMat 410) (codeMat 279) (codeMat 130) = codeMat 192 := by
      unfold actionA
      rw [step109wc220s1_QtInv]
      show (codeMat 410 : Mat3).transpose * codeMat 130 * (codeMat 279 : Mat3).transpose = codeMat 192
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 40 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 410) (codeMat 279) (codeMat 40) = codeMat 36 := by
      unfold actionA
      rw [step109wc220s1_QtInv]
      show (codeMat 410 : Mat3).transpose * codeMat 40 * (codeMat 279 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 3 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 410) (codeMat 279) (codeMat 3) = codeMat 16 := by
      unfold actionA
      rw [step109wc220s1_QtInv]
      show (codeMat 410 : Mat3).transpose * codeMat 3 * (codeMat 279 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 410) (codeMat 279) (codeMat 1) = codeMat 8 := by
      unfold actionA
      rw [step109wc220s1_QtInv]
      show (codeMat 410 : Mat3).transpose * codeMat 1 * (codeMat 279 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 9 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 9 (by decide)
    have hact : actionA (codeMat 410) (codeMat 279) (codeMat 9) = codeMat 1 := by
      unfold actionA
      rw [step109wc220s1_QtInv]
      show (codeMat 410 : Mat3).transpose * codeMat 9 * (codeMat 279 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact

theorem step109wc220s1Dispatch :
    QuotientRankAtLeast (o220SourceU_wc ⟨1, by omega⟩) 12 := by
  have hP : Invertible (codeMat 410 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 279 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 410) (codeMat 279) o43W_mono) 12 :=
    @quotientRankAtLeast_action (codeMat 410) (codeMat 279) hP hQ o43W_mono 12
      orbit43_lb12_mono
  exact quotientRankAtLeast_mono step109wc220s1_contain hAct


private theorem step109wc220s2_QtInv :
    (codeMat 270 : Mat3).transpose⁻¹ = (codeMat 298 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 270 : Mat3).transpose * (codeMat 298 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc220s2_contain :
    (o220SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 84) (codeMat 270) orbit14W := by
  change spanCodes [264, 128, 64, 34, 16, 6, 1] ≤ actionW (codeMat 84) (codeMat 270) orbit14W
  apply step109wc220_spanCodes_le_of_gens [264, 128, 64, 34, 16, 6, 1]
    (actionW (codeMat 84) (codeMat 270) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 21 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 21 (by decide)
    have hact : actionA (codeMat 84) (codeMat 270) (codeMat 21) = codeMat 264 := by
      unfold actionA
      rw [step109wc220s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 21 * (codeMat 298 : Mat3).transpose = codeMat 264
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 270) (codeMat 1) = codeMat 128 := by
      unfold actionA
      rw [step109wc220s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 298 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 270) (codeMat 2) = codeMat 64 := by
      unfold actionA
      rw [step109wc220s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 298 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 104 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 104 (by decide)
    have hact : actionA (codeMat 84) (codeMat 270) (codeMat 104) = codeMat 34 := by
      unfold actionA
      rw [step109wc220s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 104 * (codeMat 298 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 270) (codeMat 8) = codeMat 16 := by
      unfold actionA
      rw [step109wc220s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 298 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 270) (codeMat 256) = codeMat 6 := by
      unfold actionA
      rw [step109wc220s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 298 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 270) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc220s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 298 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact

theorem step109wc220s2Dispatch :
    QuotientRankAtLeast (o220SourceU_wc ⟨2, by omega⟩) 12 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 270 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 270) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 270) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc220s2_contain hAct


private theorem step109wc220s3_QtInv :
    (codeMat 98 : Mat3).transpose⁻¹ = (codeMat 140 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 98 : Mat3).transpose * (codeMat 140 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc220s3_contain :
    (o220SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 106) (codeMat 98) orbit14W := by
  change spanCodes [264, 130, 66, 32, 16, 4, 1] ≤ actionW (codeMat 106) (codeMat 98) orbit14W
  apply step109wc220_spanCodes_le_of_gens [264, 130, 66, 32, 16, 4, 1]
    (actionW (codeMat 106) (codeMat 98) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 148 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 148 (by decide)
    have hact : actionA (codeMat 106) (codeMat 98) (codeMat 148) = codeMat 264 := by
      unfold actionA
      rw [step109wc220s3_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 148 * (codeMat 140 : Mat3).transpose = codeMat 264
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 106) (codeMat 98) (codeMat 8) = codeMat 130 := by
      unfold actionA
      rw [step109wc220s3_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 8 * (codeMat 140 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 352 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 352 (by decide)
    have hact : actionA (codeMat 106) (codeMat 98) (codeMat 352) = codeMat 66 := by
      unfold actionA
      rw [step109wc220s3_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 352 * (codeMat 140 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 106) (codeMat 98) (codeMat 2) = codeMat 32 := by
      unfold actionA
      rw [step109wc220s3_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 2 * (codeMat 140 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 106) (codeMat 98) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step109wc220s3_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 1 * (codeMat 140 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 106) (codeMat 98) (codeMat 128) = codeMat 4 := by
      unfold actionA
      rw [step109wc220s3_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 128 * (codeMat 140 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 106) (codeMat 98) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc220s3_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 256 * (codeMat 140 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact

theorem step109wc220s3Dispatch :
    QuotientRankAtLeast (o220SourceU_wc ⟨3, by omega⟩) 12 := by
  have hP : Invertible (codeMat 106 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 106) (codeMat 98) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 106) (codeMat 98) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc220s3_contain hAct


private theorem step109wc220s4_QtInv :
    (codeMat 212 : Mat3).transpose⁻¹ = (codeMat 86 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 212 : Mat3).transpose * (codeMat 86 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc220s4_contain :
    (o220SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 92) (codeMat 212) orbit10W := by
  change spanCodes [256, 132, 68, 36, 16, 10, 1] ≤ actionW (codeMat 92) (codeMat 212) orbit10W
  apply step109wc220_spanCodes_le_of_gens [256, 132, 68, 36, 16, 10, 1]
    (actionW (codeMat 92) (codeMat 212) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 92) (codeMat 212) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step109wc220s4_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 1 * (codeMat 86 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 70 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 70 (by decide)
    have hact : actionA (codeMat 92) (codeMat 212) (codeMat 70) = codeMat 132 := by
      unfold actionA
      rw [step109wc220s4_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 70 * (codeMat 86 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 92) (codeMat 212) (codeMat 68) = codeMat 68 := by
      unfold actionA
      rw [step109wc220s4_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 68 * (codeMat 86 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 92) (codeMat 212) (codeMat 8) = codeMat 36 := by
      unfold actionA
      rw [step109wc220s4_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 8 * (codeMat 86 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 432 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 432 (by decide)
    have hact : actionA (codeMat 92) (codeMat 212) (codeMat 432) = codeMat 16 := by
      unfold actionA
      rw [step109wc220s4_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 432 * (codeMat 86 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 92) (codeMat 212) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step109wc220s4_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 160 * (codeMat 86 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 92) (codeMat 212) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc220s4_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 256 * (codeMat 86 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact

theorem step109wc220s4Dispatch :
    QuotientRankAtLeast (o220SourceU_wc ⟨4, by omega⟩) 12 := by
  have hP : Invertible (codeMat 92 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 212 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 92) (codeMat 212) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 92) (codeMat 212) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc220s4_contain hAct


private theorem step109wc220s5_QtInv :
    (codeMat 492 : Mat3).transpose⁻¹ = (codeMat 115 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 492 : Mat3).transpose * (codeMat 115 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc220s5_contain :
    (o220SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 84) (codeMat 492) flatW_3 := by
  change spanCodes [260, 132, 68, 36, 16, 12, 2, 1] ≤ actionW (codeMat 84) (codeMat 492) flatW_3
  apply step109wc220_spanCodes_le_of_gens [260, 132, 68, 36, 16, 12, 2, 1]
    (actionW (codeMat 84) (codeMat 492) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 455 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 455 (by decide)
    have hact : actionA (codeMat 84) (codeMat 492) (codeMat 455) = codeMat 260 := by
      unfold actionA
      rw [step109wc220s5_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 455 * (codeMat 115 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 452 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 452 (by decide)
    have hact : actionA (codeMat 84) (codeMat 492) (codeMat 452) = codeMat 132 := by
      unfold actionA
      rw [step109wc220s5_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 452 * (codeMat 115 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 454 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 454 (by decide)
    have hact : actionA (codeMat 84) (codeMat 492) (codeMat 454) = codeMat 68 := by
      unfold actionA
      rw [step109wc220s5_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 454 * (codeMat 115 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 504 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 504 (by decide)
    have hact : actionA (codeMat 84) (codeMat 492) (codeMat 504) = codeMat 36 := by
      unfold actionA
      rw [step109wc220s5_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 504 * (codeMat 115 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 32 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 84) (codeMat 492) (codeMat 32) = codeMat 16 := by
      unfold actionA
      rw [step109wc220s5_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 32 * (codeMat 115 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 496 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 496 (by decide)
    have hact : actionA (codeMat 84) (codeMat 492) (codeMat 496) = codeMat 12 := by
      unfold actionA
      rw [step109wc220s5_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 496 * (codeMat 115 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 492) (codeMat 256) = codeMat 2 := by
      unfold actionA
      rw [step109wc220s5_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 115 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 492) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step109wc220s5_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 115 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc220_codeMat_mem_actionW_of_witness hw hact

theorem step109wc220s5Dispatch :
    QuotientRankAtLeast (o220SourceU_wc ⟨5, by omega⟩) 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 492 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 492) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 492) hP hQ flatW_3 9
      flatSeed_3
  exact quotientRankAtLeast_mono step109wc220s5_contain hAct

theorem step109wc220_all_dispatch (i : Fin 6) :
    QuotientRankAtLeast (o220SourceU_wc i) (o220SourceLb_wc i) := by
  fin_cases i
  · exact step109wc220s0Dispatch
  · exact step109wc220s1Dispatch
  · exact step109wc220s2Dispatch
  · exact step109wc220s3Dispatch
  · exact step109wc220s4Dispatch
  · exact step109wc220s5Dispatch

theorem step109_orbit220_lb15_wc : QuotientRankAtLeast o220W_wc 15 :=
  o220Lb15_wc step109wc220_all_dispatch

end QiushiMatmul
