import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit202Consumer
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit76Dispatch
import QiushiWcOrbit47Dispatch
import QiushiStep99Orbit68Dispatch

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc202_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc202_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc202s0_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc202s0_contain :
    (o202SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 266) (codeMat 266) o65W := by
  change spanCodes [288, 160, 68, 16, 10, 1] ≤ actionW (codeMat 266) (codeMat 266) o65W
  apply step109wc202_spanCodes_le_of_gens [288, 160, 68, 16, 10, 1]
    (actionW (codeMat 266) (codeMat 266) o65W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 260 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 260 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 260) = codeMat 288 := by
      unfold actionA
      rw [step109wc202s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 260 * (codeMat 266 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 68 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 68) = codeMat 160 := by
      unfold actionA
      rw [step109wc202s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 68 * (codeMat 266 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 160 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 160) = codeMat 68 := by
      unfold actionA
      rw [step109wc202s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 160 * (codeMat 266 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step109wc202s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 10 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step109wc202s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 10 * (codeMat 266 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc202s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact

theorem step109wc202s0Dispatch :
    QuotientRankAtLeast (o202SourceU_wc ⟨0, by omega⟩) 15 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 266) o65W) 15 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 266) hP hQ o65W 15
      step99_orbit65_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc202s0_contain hAct


private theorem step109wc202s1_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = (codeMat 275 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * (codeMat 275 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc202s1_contain :
    (o202SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 281) (codeMat 275) o76W := by
  change spanCodes [292, 160, 68, 20, 10, 1] ≤ actionW (codeMat 281) (codeMat 275) o76W
  apply step109wc202_spanCodes_le_of_gens [292, 160, 68, 20, 10, 1]
    (actionW (codeMat 281) (codeMat 275) o76W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 288 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 288 (by decide)
    have hact : actionA (codeMat 281) (codeMat 275) (codeMat 288) = codeMat 292 := by
      unfold actionA
      rw [step109wc202s1_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 288 * (codeMat 275 : Mat3).transpose = codeMat 292
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 228 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 228 (by decide)
    have hact : actionA (codeMat 281) (codeMat 275) (codeMat 228) = codeMat 160 := by
      unfold actionA
      rw [step109wc202s1_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 228 * (codeMat 275 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 281) (codeMat 275) (codeMat 68) = codeMat 68 := by
      unfold actionA
      rw [step109wc202s1_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 68 * (codeMat 275 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 31 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 31 (by decide)
    have hact : actionA (codeMat 281) (codeMat 275) (codeMat 31) = codeMat 20 := by
      unfold actionA
      rw [step109wc202s1_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 31 * (codeMat 275 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 10 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 281) (codeMat 275) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step109wc202s1_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 10 * (codeMat 275 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 281) (codeMat 275) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc202s1_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 1 * (codeMat 275 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact

theorem step109wc202s1Dispatch :
    QuotientRankAtLeast (o202SourceU_wc ⟨1, by omega⟩) 15 := by
  have hP : Invertible (codeMat 281 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 281) (codeMat 275) o76W) 15 :=
    @quotientRankAtLeast_action (codeMat 281) (codeMat 275) hP hQ o76W 15
      step99_orbit76_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc202s1_contain hAct


private theorem step109wc202s2_QtInv :
    (codeMat 311 : Mat3).transpose⁻¹ = (codeMat 307 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 311 : Mat3).transpose * (codeMat 307 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc202s2_contain :
    (o202SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 409) (codeMat 311) o76W := by
  change spanCodes [294, 160, 68, 22, 10, 1] ≤ actionW (codeMat 409) (codeMat 311) o76W
  apply step109wc202_spanCodes_le_of_gens [294, 160, 68, 22, 10, 1]
    (actionW (codeMat 409) (codeMat 311) o76W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 452 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 452 (by decide)
    have hact : actionA (codeMat 409) (codeMat 311) (codeMat 452) = codeMat 294 := by
      unfold actionA
      rw [step109wc202s2_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 452 * (codeMat 307 : Mat3).transpose = codeMat 294
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 228 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 228 (by decide)
    have hact : actionA (codeMat 409) (codeMat 311) (codeMat 228) = codeMat 160 := by
      unfold actionA
      rw [step109wc202s2_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 228 * (codeMat 307 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 78 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 78 (by decide)
    have hact : actionA (codeMat 409) (codeMat 311) (codeMat 78) = codeMat 68 := by
      unfold actionA
      rw [step109wc202s2_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 78 * (codeMat 307 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 31 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 31 (by decide)
    have hact : actionA (codeMat 409) (codeMat 311) (codeMat 31) = codeMat 22 := by
      unfold actionA
      rw [step109wc202s2_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 31 * (codeMat 307 : Mat3).transpose = codeMat 22
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 10 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 409) (codeMat 311) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step109wc202s2_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 10 * (codeMat 307 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 409) (codeMat 311) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc202s2_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 1 * (codeMat 307 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact

theorem step109wc202s2Dispatch :
    QuotientRankAtLeast (o202SourceU_wc ⟨2, by omega⟩) 15 := by
  have hP : Invertible (codeMat 409 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 311 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 409) (codeMat 311) o76W) 15 :=
    @quotientRankAtLeast_action (codeMat 409) (codeMat 311) hP hQ o76W 15
      step99_orbit76_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc202s2_contain hAct


private theorem step109wc202s3_QtInv :
    (codeMat 396 : Mat3).transpose⁻¹ = (codeMat 106 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 396 : Mat3).transpose * (codeMat 106 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc202s3_contain :
    (o202SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 142) (codeMat 396) o65W := by
  change spanCodes [272, 128, 68, 32, 10, 1] ≤ actionW (codeMat 142) (codeMat 396) o65W
  apply step109wc202_spanCodes_le_of_gens [272, 128, 68, 32, 10, 1]
    (actionW (codeMat 142) (codeMat 396) o65W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 69 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 69 (by decide)
    have hact : actionA (codeMat 142) (codeMat 396) (codeMat 69) = codeMat 272 := by
      unfold actionA
      rw [step109wc202s3_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 69 * (codeMat 106 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 260 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 260 (by decide)
    have hact : actionA (codeMat 142) (codeMat 396) (codeMat 260) = codeMat 128 := by
      unfold actionA
      rw [step109wc202s3_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 260 * (codeMat 106 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 170 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 170 (by decide)
    have hact : actionA (codeMat 142) (codeMat 396) (codeMat 170) = codeMat 68 := by
      unfold actionA
      rw [step109wc202s3_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 170 * (codeMat 106 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 320 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 320 (by decide)
    have hact : actionA (codeMat 142) (codeMat 396) (codeMat 320) = codeMat 32 := by
      unfold actionA
      rw [step109wc202s3_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 320 * (codeMat 106 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 160 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 142) (codeMat 396) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step109wc202s3_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 160 * (codeMat 106 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 142) (codeMat 396) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc202s3_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 16 * (codeMat 106 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact

theorem step109wc202s3Dispatch :
    QuotientRankAtLeast (o202SourceU_wc ⟨3, by omega⟩) 15 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 396 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 396) o65W) 15 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 396) hP hQ o65W 15
      step99_orbit65_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc202s3_contain hAct


private theorem step109wc202s4_QtInv :
    (codeMat 421 : Mat3).transpose⁻¹ = (codeMat 179 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 421 : Mat3).transpose * (codeMat 179 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc202s4_contain :
    (o202SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 185) (codeMat 421) o76W := by
  change spanCodes [274, 130, 68, 34, 10, 1] ≤ actionW (codeMat 185) (codeMat 421) o76W
  apply step109wc202_spanCodes_le_of_gens [274, 130, 68, 34, 10, 1]
    (actionW (codeMat 185) (codeMat 421) o76W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 251 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 251 (by decide)
    have hact : actionA (codeMat 185) (codeMat 421) (codeMat 251) = codeMat 274 := by
      unfold actionA
      rw [step109wc202s4_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 251 * (codeMat 179 : Mat3).transpose = codeMat 274
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 288 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 288 (by decide)
    have hact : actionA (codeMat 185) (codeMat 421) (codeMat 288) = codeMat 130 := by
      unfold actionA
      rw [step109wc202s4_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 288 * (codeMat 179 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 78 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 78 (by decide)
    have hact : actionA (codeMat 185) (codeMat 421) (codeMat 78) = codeMat 68 := by
      unfold actionA
      rw [step109wc202s4_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 78 * (codeMat 179 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 452 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 452 (by decide)
    have hact : actionA (codeMat 185) (codeMat 421) (codeMat 452) = codeMat 34 := by
      unfold actionA
      rw [step109wc202s4_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 452 * (codeMat 179 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 68 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 185) (codeMat 421) (codeMat 68) = codeMat 10 := by
      unfold actionA
      rw [step109wc202s4_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 68 * (codeMat 179 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 185) (codeMat 421) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc202s4_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 1 * (codeMat 179 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact

theorem step109wc202s4Dispatch :
    QuotientRankAtLeast (o202SourceU_wc ⟨4, by omega⟩) 15 := by
  have hP : Invertible (codeMat 185 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 421 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 185) (codeMat 421) o76W) 15 :=
    @quotientRankAtLeast_action (codeMat 185) (codeMat 421) hP hQ o76W 15
      step99_orbit76_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc202s4_contain hAct


private theorem step109wc202s5_QtInv :
    (codeMat 403 : Mat3).transpose⁻¹ = (codeMat 403 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 403 : Mat3).transpose * (codeMat 403 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc202s5_contain :
    (o202SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 313) (codeMat 403) o76W := by
  change spanCodes [276, 132, 68, 36, 10, 1] ≤ actionW (codeMat 313) (codeMat 403) o76W
  apply step109wc202_spanCodes_le_of_gens [276, 132, 68, 36, 10, 1]
    (actionW (codeMat 313) (codeMat 403) o76W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 251 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 251 (by decide)
    have hact : actionA (codeMat 313) (codeMat 403) (codeMat 251) = codeMat 276 := by
      unfold actionA
      rw [step109wc202s5_QtInv]
      show (codeMat 313 : Mat3).transpose * codeMat 251 * (codeMat 403 : Mat3).transpose = codeMat 276
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 452 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 452 (by decide)
    have hact : actionA (codeMat 313) (codeMat 403) (codeMat 452) = codeMat 132 := by
      unfold actionA
      rw [step109wc202s5_QtInv]
      show (codeMat 313 : Mat3).transpose * codeMat 452 * (codeMat 403 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 313) (codeMat 403) (codeMat 68) = codeMat 68 := by
      unfold actionA
      rw [step109wc202s5_QtInv]
      show (codeMat 313 : Mat3).transpose * codeMat 68 * (codeMat 403 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 288 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 288 (by decide)
    have hact : actionA (codeMat 313) (codeMat 403) (codeMat 288) = codeMat 36 := by
      unfold actionA
      rw [step109wc202s5_QtInv]
      show (codeMat 313 : Mat3).transpose * codeMat 288 * (codeMat 403 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 78 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 78 (by decide)
    have hact : actionA (codeMat 313) (codeMat 403) (codeMat 78) = codeMat 10 := by
      unfold actionA
      rw [step109wc202s5_QtInv]
      show (codeMat 313 : Mat3).transpose * codeMat 78 * (codeMat 403 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 313) (codeMat 403) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc202s5_QtInv]
      show (codeMat 313 : Mat3).transpose * codeMat 1 * (codeMat 403 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact

theorem step109wc202s5Dispatch :
    QuotientRankAtLeast (o202SourceU_wc ⟨5, by omega⟩) 15 := by
  have hP : Invertible (codeMat 313 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 403 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 313) (codeMat 403) o76W) 15 :=
    @quotientRankAtLeast_action (codeMat 313) (codeMat 403) hP hQ o76W 15
      step99_orbit76_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc202s5_contain hAct


private theorem step109wc202s6_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc202s6_contain :
    (o202SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 140) (codeMat 140) o65W := by
  change spanCodes [256, 144, 68, 48, 10, 1] ≤ actionW (codeMat 140) (codeMat 140) o65W
  apply step109wc202_spanCodes_le_of_gens [256, 144, 68, 48, 10, 1]
    (actionW (codeMat 140) (codeMat 140) o65W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 1 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 140) (codeMat 140) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step109wc202s6_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 260 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 260 (by decide)
    have hact : actionA (codeMat 140) (codeMat 140) (codeMat 260) = codeMat 144 := by
      unfold actionA
      rw [step109wc202s6_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 260 * (codeMat 98 : Mat3).transpose = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 10 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 140) (codeMat 140) (codeMat 10) = codeMat 68 := by
      unfold actionA
      rw [step109wc202s6_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 10 * (codeMat 98 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 320 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 320 (by decide)
    have hact : actionA (codeMat 140) (codeMat 140) (codeMat 320) = codeMat 48 := by
      unfold actionA
      rw [step109wc202s6_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 320 * (codeMat 98 : Mat3).transpose = codeMat 48
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 160 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 140) (codeMat 140) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step109wc202s6_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 160 * (codeMat 98 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 140) (codeMat 140) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc202s6_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 16 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact

theorem step109wc202s6Dispatch :
    QuotientRankAtLeast (o202SourceU_wc ⟨6, by omega⟩) 15 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 140) o65W) 15 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 140) hP hQ o65W 15
      step99_orbit65_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc202s6_contain hAct


private theorem step109wc202s7_QtInv :
    (codeMat 165 : Mat3).transpose⁻¹ = (codeMat 163 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 165 : Mat3).transpose * (codeMat 163 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc202s7_contain :
    (o202SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 169) (codeMat 165) o76W := by
  change spanCodes [258, 146, 68, 50, 10, 1] ≤ actionW (codeMat 169) (codeMat 165) o76W
  apply step109wc202_spanCodes_le_of_gens [258, 146, 68, 50, 10, 1]
    (actionW (codeMat 169) (codeMat 165) o76W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 31 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 31 (by decide)
    have hact : actionA (codeMat 169) (codeMat 165) (codeMat 31) = codeMat 258 := by
      unfold actionA
      rw [step109wc202s7_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 31 * (codeMat 163 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 288 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 288 (by decide)
    have hact : actionA (codeMat 169) (codeMat 165) (codeMat 288) = codeMat 146 := by
      unfold actionA
      rw [step109wc202s7_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 288 * (codeMat 163 : Mat3).transpose = codeMat 146
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 10 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 169) (codeMat 165) (codeMat 10) = codeMat 68 := by
      unfold actionA
      rw [step109wc202s7_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 10 * (codeMat 163 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 452 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 452 (by decide)
    have hact : actionA (codeMat 169) (codeMat 165) (codeMat 452) = codeMat 50 := by
      unfold actionA
      rw [step109wc202s7_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 452 * (codeMat 163 : Mat3).transpose = codeMat 50
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 68 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 169) (codeMat 165) (codeMat 68) = codeMat 10 := by
      unfold actionA
      rw [step109wc202s7_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 68 * (codeMat 163 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 165) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc202s7_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * (codeMat 163 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact

theorem step109wc202s7Dispatch :
    QuotientRankAtLeast (o202SourceU_wc ⟨7, by omega⟩) 15 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 165 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 165) o76W) 15 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 165) hP hQ o76W 15
      step99_orbit76_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc202s7_contain hAct


private theorem step109wc202s8_QtInv :
    (codeMat 183 : Mat3).transpose⁻¹ = (codeMat 419 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 183 : Mat3).transpose * (codeMat 419 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc202s8_contain :
    (o202SourceU_wc ⟨8, by omega⟩) ≤ actionW (codeMat 425) (codeMat 183) o76W := by
  change spanCodes [262, 150, 68, 54, 10, 1] ≤ actionW (codeMat 425) (codeMat 183) o76W
  apply step109wc202_spanCodes_le_of_gens [262, 150, 68, 54, 10, 1]
    (actionW (codeMat 425) (codeMat 183) o76W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 31 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 31 (by decide)
    have hact : actionA (codeMat 425) (codeMat 183) (codeMat 31) = codeMat 262 := by
      unfold actionA
      rw [step109wc202s8_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 31 * (codeMat 419 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 452 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 452 (by decide)
    have hact : actionA (codeMat 425) (codeMat 183) (codeMat 452) = codeMat 150 := by
      unfold actionA
      rw [step109wc202s8_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 452 * (codeMat 419 : Mat3).transpose = codeMat 150
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 10 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 425) (codeMat 183) (codeMat 10) = codeMat 68 := by
      unfold actionA
      rw [step109wc202s8_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 10 * (codeMat 419 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 288 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 288 (by decide)
    have hact : actionA (codeMat 425) (codeMat 183) (codeMat 288) = codeMat 54 := by
      unfold actionA
      rw [step109wc202s8_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 288 * (codeMat 419 : Mat3).transpose = codeMat 54
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 78 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 78 (by decide)
    have hact : actionA (codeMat 425) (codeMat 183) (codeMat 78) = codeMat 10 := by
      unfold actionA
      rw [step109wc202s8_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 78 * (codeMat 419 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 425) (codeMat 183) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc202s8_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 1 * (codeMat 419 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact

theorem step109wc202s8Dispatch :
    QuotientRankAtLeast (o202SourceU_wc ⟨8, by omega⟩) 15 := by
  have hP : Invertible (codeMat 425 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 183 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 425) (codeMat 183) o76W) 15 :=
    @quotientRankAtLeast_action (codeMat 425) (codeMat 183) hP hQ o76W 15
      step99_orbit76_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc202s8_contain hAct


private theorem step109wc202s9_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc202s9_contain :
    (o202SourceU_wc ⟨9, by omega⟩) ≤ actionW (codeMat 273) (codeMat 273) o47W_wc := by
  change spanCodes [304, 160, 68, 8, 2, 1] ≤ actionW (codeMat 273) (codeMat 273) o47W_wc
  apply step109wc202_spanCodes_le_of_gens [304, 160, 68, 8, 2, 1]
    (actionW (codeMat 273) (codeMat 273) o47W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 304 ∈ o47W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [304, 160, 68, 8, 2, 1] 304 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 304) = codeMat 304 := by
      unfold actionA
      rw [step109wc202s9_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 304 * (codeMat 273 : Mat3).transpose = codeMat 304
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ o47W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [304, 160, 68, 8, 2, 1] 160 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 160) = codeMat 160 := by
      unfold actionA
      rw [step109wc202s9_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 160 * (codeMat 273 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ o47W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [304, 160, 68, 8, 2, 1] 68 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 68) = codeMat 68 := by
      unfold actionA
      rw [step109wc202s9_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 68 * (codeMat 273 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ o47W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [304, 160, 68, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step109wc202s9_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 273 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o47W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [304, 160, 68, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc202s9_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o47W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [304, 160, 68, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc202s9_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact

theorem step109wc202s9Dispatch :
    QuotientRankAtLeast (o202SourceU_wc ⟨9, by omega⟩) 14 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 273) o47W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 273) hP hQ o47W_wc 14
      step109_orbit47_lb14_wc
  exact quotientRankAtLeast_mono step109wc202s9_contain hAct


private theorem step109wc202s10_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc202s10_contain :
    (o202SourceU_wc ⟨10, by omega⟩) ≤ actionW (codeMat 161) (codeMat 161) o47W_wc := by
  change spanCodes [304, 160, 64, 10, 4, 1] ≤ actionW (codeMat 161) (codeMat 161) o47W_wc
  apply step109wc202_spanCodes_le_of_gens [304, 160, 64, 10, 4, 1]
    (actionW (codeMat 161) (codeMat 161) o47W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 400 ∈ o47W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [304, 160, 68, 8, 2, 1] 400 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 400) = codeMat 304 := by
      unfold actionA
      rw [step109wc202s10_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 400 * (codeMat 161 : Mat3).transpose = codeMat 304
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ o47W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [304, 160, 68, 8, 2, 1] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 160) = codeMat 160 := by
      unfold actionA
      rw [step109wc202s10_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * (codeMat 161 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ o47W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [304, 160, 68, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 8) = codeMat 64 := by
      unfold actionA
      rw [step109wc202s10_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 8 * (codeMat 161 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 68 ∈ o47W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [304, 160, 68, 8, 2, 1] 68 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 68) = codeMat 10 := by
      unfold actionA
      rw [step109wc202s10_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 68 * (codeMat 161 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o47W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [304, 160, 68, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 2) = codeMat 4 := by
      unfold actionA
      rw [step109wc202s10_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 161 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o47W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [304, 160, 68, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc202s10_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact

theorem step109wc202s10Dispatch :
    QuotientRankAtLeast (o202SourceU_wc ⟨10, by omega⟩) 14 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 161) o47W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 161) hP hQ o47W_wc 14
      step109_orbit47_lb14_wc
  exact quotientRankAtLeast_mono step109wc202s10_contain hAct


private theorem step109wc202s11_QtInv :
    (codeMat 417 : Mat3).transpose⁻¹ = (codeMat 177 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 417 : Mat3).transpose * (codeMat 177 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc202s11_contain :
    (o202SourceU_wc ⟨11, by omega⟩) ≤ actionW (codeMat 177) (codeMat 417) o47W_wc := by
  change spanCodes [304, 160, 66, 10, 6, 1] ≤ actionW (codeMat 177) (codeMat 417) o47W_wc
  apply step109wc202_spanCodes_le_of_gens [304, 160, 66, 10, 6, 1]
    (actionW (codeMat 177) (codeMat 417) o47W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 304 ∈ o47W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [304, 160, 68, 8, 2, 1] 304 (by decide)
    have hact : actionA (codeMat 177) (codeMat 417) (codeMat 304) = codeMat 304 := by
      unfold actionA
      rw [step109wc202s11_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 304 * (codeMat 177 : Mat3).transpose = codeMat 304
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ o47W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [304, 160, 68, 8, 2, 1] 160 (by decide)
    have hact : actionA (codeMat 177) (codeMat 417) (codeMat 160) = codeMat 160 := by
      unfold actionA
      rw [step109wc202s11_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 160 * (codeMat 177 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 76 ∈ o47W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [304, 160, 68, 8, 2, 1] 76 (by decide)
    have hact : actionA (codeMat 177) (codeMat 417) (codeMat 76) = codeMat 66 := by
      unfold actionA
      rw [step109wc202s11_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 76 * (codeMat 177 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 68 ∈ o47W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [304, 160, 68, 8, 2, 1] 68 (by decide)
    have hact : actionA (codeMat 177) (codeMat 417) (codeMat 68) = codeMat 10 := by
      unfold actionA
      rw [step109wc202s11_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 68 * (codeMat 177 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o47W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [304, 160, 68, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 177) (codeMat 417) (codeMat 2) = codeMat 6 := by
      unfold actionA
      rw [step109wc202s11_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 2 * (codeMat 177 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o47W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [304, 160, 68, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 417) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc202s11_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * (codeMat 177 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact

theorem step109wc202s11Dispatch :
    QuotientRankAtLeast (o202SourceU_wc ⟨11, by omega⟩) 14 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 417) o47W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 417) hP hQ o47W_wc 14
      step109_orbit47_lb14_wc
  exact quotientRankAtLeast_mono step109wc202s11_contain hAct


private theorem step109wc202s12_QtInv :
    (codeMat 279 : Mat3).transpose⁻¹ = (codeMat 279 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 279 : Mat3).transpose * (codeMat 279 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc202s12_contain :
    (o202SourceU_wc ⟨12, by omega⟩) ≤ actionW (codeMat 337) (codeMat 279) o68W := by
  change spanCodes [290, 160, 68, 18, 10, 1] ≤ actionW (codeMat 337) (codeMat 279) o68W
  apply step109wc202_spanCodes_le_of_gens [290, 160, 68, 18, 10, 1]
    (actionW (codeMat 337) (codeMat 279) o68W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 366 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 366 (by decide)
    have hact : actionA (codeMat 337) (codeMat 279) (codeMat 366) = codeMat 290 := by
      unfold actionA
      rw [step109wc202s12_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 366 * (codeMat 279 : Mat3).transpose = codeMat 290
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 235 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 235 (by decide)
    have hact : actionA (codeMat 337) (codeMat 279) (codeMat 235) = codeMat 160 := by
      unfold actionA
      rw [step109wc202s12_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 235 * (codeMat 279 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 337) (codeMat 279) (codeMat 68) = codeMat 68 := by
      unfold actionA
      rw [step109wc202s12_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 68 * (codeMat 279 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 27 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 27 (by decide)
    have hact : actionA (codeMat 337) (codeMat 279) (codeMat 27) = codeMat 18 := by
      unfold actionA
      rw [step109wc202s12_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 27 * (codeMat 279 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 11 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 337) (codeMat 279) (codeMat 11) = codeMat 10 := by
      unfold actionA
      rw [step109wc202s12_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 11 * (codeMat 279 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 337) (codeMat 279) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc202s12_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 1 * (codeMat 279 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact

theorem step109wc202s12Dispatch :
    QuotientRankAtLeast (o202SourceU_wc ⟨12, by omega⟩) 14 := by
  have hP : Invertible (codeMat 337 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 279 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 337) (codeMat 279) o68W) 14 :=
    @quotientRankAtLeast_action (codeMat 337) (codeMat 279) hP hQ o68W 14
      step99_orbit68_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc202s12_contain hAct


private theorem step109wc202s13_QtInv :
    (codeMat 419 : Mat3).transpose⁻¹ = (codeMat 183 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 419 : Mat3).transpose * (codeMat 183 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc202s13_contain :
    (o202SourceU_wc ⟨13, by omega⟩) ≤ actionW (codeMat 241) (codeMat 419) o68W := by
  change spanCodes [278, 134, 68, 38, 10, 1] ≤ actionW (codeMat 241) (codeMat 419) o68W
  apply step109wc202_spanCodes_le_of_gens [278, 134, 68, 38, 10, 1]
    (actionW (codeMat 241) (codeMat 419) o68W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 240 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 240 (by decide)
    have hact : actionA (codeMat 241) (codeMat 419) (codeMat 240) = codeMat 278 := by
      unfold actionA
      rw [step109wc202s13_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 240 * (codeMat 183 : Mat3).transpose = codeMat 278
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 366 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 366 (by decide)
    have hact : actionA (codeMat 241) (codeMat 419) (codeMat 366) = codeMat 134 := by
      unfold actionA
      rw [step109wc202s13_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 366 * (codeMat 183 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 79 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 79 (by decide)
    have hact : actionA (codeMat 241) (codeMat 419) (codeMat 79) = codeMat 68 := by
      unfold actionA
      rw [step109wc202s13_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 79 * (codeMat 183 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 389 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 389 (by decide)
    have hact : actionA (codeMat 241) (codeMat 419) (codeMat 389) = codeMat 38 := by
      unfold actionA
      rw [step109wc202s13_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 389 * (codeMat 183 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 68 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 241) (codeMat 419) (codeMat 68) = codeMat 10 := by
      unfold actionA
      rw [step109wc202s13_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 68 * (codeMat 183 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 241) (codeMat 419) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc202s13_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 1 * (codeMat 183 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact

theorem step109wc202s13Dispatch :
    QuotientRankAtLeast (o202SourceU_wc ⟨13, by omega⟩) 14 := by
  have hP : Invertible (codeMat 241 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 419 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 241) (codeMat 419) o68W) 14 :=
    @quotientRankAtLeast_action (codeMat 241) (codeMat 419) hP hQ o68W 14
      step99_orbit68_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc202s13_contain hAct


private theorem step109wc202s14_QtInv :
    (codeMat 167 : Mat3).transpose⁻¹ = (codeMat 167 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 167 : Mat3).transpose * (codeMat 167 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc202s14_contain :
    (o202SourceU_wc ⟨14, by omega⟩) ≤ actionW (codeMat 225) (codeMat 167) o68W := by
  change spanCodes [260, 148, 68, 52, 10, 1] ≤ actionW (codeMat 225) (codeMat 167) o68W
  apply step109wc202_spanCodes_le_of_gens [260, 148, 68, 52, 10, 1]
    (actionW (codeMat 225) (codeMat 167) o68W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 27 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 27 (by decide)
    have hact : actionA (codeMat 225) (codeMat 167) (codeMat 27) = codeMat 260 := by
      unfold actionA
      rw [step109wc202s14_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 27 * (codeMat 167 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 366 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 366 (by decide)
    have hact : actionA (codeMat 225) (codeMat 167) (codeMat 366) = codeMat 148 := by
      unfold actionA
      rw [step109wc202s14_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 366 * (codeMat 167 : Mat3).transpose = codeMat 148
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 11 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 225) (codeMat 167) (codeMat 11) = codeMat 68 := by
      unfold actionA
      rw [step109wc202s14_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 11 * (codeMat 167 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 389 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 389 (by decide)
    have hact : actionA (codeMat 225) (codeMat 167) (codeMat 389) = codeMat 52 := by
      unfold actionA
      rw [step109wc202s14_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 389 * (codeMat 167 : Mat3).transpose = codeMat 52
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 68 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 225) (codeMat 167) (codeMat 68) = codeMat 10 := by
      unfold actionA
      rw [step109wc202s14_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 68 * (codeMat 167 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 225) (codeMat 167) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc202s14_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 1 * (codeMat 167 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc202_codeMat_mem_actionW_of_witness hw hact

theorem step109wc202s14Dispatch :
    QuotientRankAtLeast (o202SourceU_wc ⟨14, by omega⟩) 14 := by
  have hP : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 167 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 225) (codeMat 167) o68W) 14 :=
    @quotientRankAtLeast_action (codeMat 225) (codeMat 167) hP hQ o68W 14
      step99_orbit68_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc202s14_contain hAct

theorem step109wc202_all_dispatch (i : Fin 15) :
    QuotientRankAtLeast (o202SourceU_wc i) (o202SourceLb_wc i) := by
  fin_cases i
  · exact step109wc202s0Dispatch
  · exact step109wc202s1Dispatch
  · exact step109wc202s2Dispatch
  · exact step109wc202s3Dispatch
  · exact step109wc202s4Dispatch
  · exact step109wc202s5Dispatch
  · exact step109wc202s6Dispatch
  · exact step109wc202s7Dispatch
  · exact step109wc202s8Dispatch
  · exact step109wc202s9Dispatch
  · exact step109wc202s10Dispatch
  · exact step109wc202s11Dispatch
  · exact step109wc202s12Dispatch
  · exact step109wc202s13Dispatch
  · exact step109wc202s14Dispatch

theorem step109_orbit202_lb16_wc : QuotientRankAtLeast o202W_wc 16 :=
  o202Lb16_wc step109wc202_all_dispatch

end QiushiMatmul
