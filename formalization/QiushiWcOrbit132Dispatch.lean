import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit132Consumer
import QiushiStep99Orbit55Dispatch
import QiushiStep99Orbit56Dispatch
import QiushiWcOrbit57Dispatch
import QiushiOrbit10FP
import QiushiFlattenSeeds

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc132_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc132_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc132s0_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc132s0_contain :
    (o132SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 345) (codeMat 273) o55W := by
  change spanCodes [276, 132, 36, 12, 2, 1] ≤ actionW (codeMat 345) (codeMat 273) o55W
  apply step109wc132_spanCodes_le_of_gens [276, 132, 36, 12, 2, 1]
    (actionW (codeMat 345) (codeMat 273) o55W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 274 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 274 (by decide)
    have hact : actionA (codeMat 345) (codeMat 273) (codeMat 274) = codeMat 276 := by
      unfold actionA
      rw [step109wc132s0_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 274 * (codeMat 273 : Mat3).transpose = codeMat 276
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 134 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 134 (by decide)
    have hact : actionA (codeMat 345) (codeMat 273) (codeMat 134) = codeMat 132 := by
      unfold actionA
      rw [step109wc132s0_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 134 * (codeMat 273 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 32 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 345) (codeMat 273) (codeMat 32) = codeMat 36 := by
      unfold actionA
      rw [step109wc132s0_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 32 * (codeMat 273 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 13 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 13 (by decide)
    have hact : actionA (codeMat 345) (codeMat 273) (codeMat 13) = codeMat 12 := by
      unfold actionA
      rw [step109wc132s0_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 13 * (codeMat 273 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 345) (codeMat 273) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc132s0_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 345) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc132s0_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact

theorem step109wc132s0Dispatch :
    QuotientRankAtLeast (o132SourceU_wc ⟨0, by omega⟩) 14 := by
  have hP : Invertible (codeMat 345 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 345) (codeMat 273) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 345) (codeMat 273) hP hQ o55W 14
      step99_orbit55_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc132s0_contain hAct


private theorem step109wc132s1_QtInv :
    (codeMat 305 : Mat3).transpose⁻¹ = (codeMat 305 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 305 : Mat3).transpose * (codeMat 305 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc132s1_contain :
    (o132SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 473) (codeMat 305) o55W := by
  change spanCodes [260, 148, 52, 12, 2, 1] ≤ actionW (codeMat 473) (codeMat 305) o55W
  apply step109wc132_spanCodes_le_of_gens [260, 148, 52, 12, 2, 1]
    (actionW (codeMat 473) (codeMat 305) o55W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 438 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 438 (by decide)
    have hact : actionA (codeMat 473) (codeMat 305) (codeMat 438) = codeMat 260 := by
      unfold actionA
      rw [step109wc132s1_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 438 * (codeMat 305 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 132 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 132 (by decide)
    have hact : actionA (codeMat 473) (codeMat 305) (codeMat 132) = codeMat 148 := by
      unfold actionA
      rw [step109wc132s1_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 132 * (codeMat 305 : Mat3).transpose = codeMat 148
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 34 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 34 (by decide)
    have hact : actionA (codeMat 473) (codeMat 305) (codeMat 34) = codeMat 52 := by
      unfold actionA
      rw [step109wc132s1_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 34 * (codeMat 305 : Mat3).transpose = codeMat 52
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 15 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 15 (by decide)
    have hact : actionA (codeMat 473) (codeMat 305) (codeMat 15) = codeMat 12 := by
      unfold actionA
      rw [step109wc132s1_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 15 * (codeMat 305 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 473) (codeMat 305) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc132s1_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 2 * (codeMat 305 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 473) (codeMat 305) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc132s1_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 1 * (codeMat 305 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact

theorem step109wc132s1Dispatch :
    QuotientRankAtLeast (o132SourceU_wc ⟨1, by omega⟩) 14 := by
  have hP : Invertible (codeMat 473 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 473) (codeMat 305) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 473) (codeMat 305) hP hQ o55W 14
      step99_orbit55_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc132s1_contain hAct


private theorem step109wc132s2_QtInv :
    (codeMat 279 : Mat3).transpose⁻¹ = (codeMat 279 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 279 : Mat3).transpose * (codeMat 279 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc132s2_contain :
    (o132SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 465) (codeMat 279) o56W := by
  change spanCodes [304, 160, 80, 12, 2, 1] ≤ actionW (codeMat 465) (codeMat 279) o56W
  apply step109wc132_spanCodes_le_of_gens [304, 160, 80, 12, 2, 1]
    (actionW (codeMat 465) (codeMat 279) o56W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 349 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 349 (by decide)
    have hact : actionA (codeMat 465) (codeMat 279) (codeMat 349) = codeMat 304 := by
      unfold actionA
      rw [step109wc132s2_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 349 * (codeMat 279 : Mat3).transpose = codeMat 304
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 243 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 243 (by decide)
    have hact : actionA (codeMat 465) (codeMat 279) (codeMat 243) = codeMat 160 := by
      unfold actionA
      rw [step109wc132s2_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 243 * (codeMat 279 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 81 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 81 (by decide)
    have hact : actionA (codeMat 465) (codeMat 279) (codeMat 81) = codeMat 80 := by
      unfold actionA
      rw [step109wc132s2_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 81 * (codeMat 279 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 13 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 13 (by decide)
    have hact : actionA (codeMat 465) (codeMat 279) (codeMat 13) = codeMat 12 := by
      unfold actionA
      rw [step109wc132s2_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 13 * (codeMat 279 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 465) (codeMat 279) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [step109wc132s2_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 3 * (codeMat 279 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 465) (codeMat 279) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc132s2_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 1 * (codeMat 279 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact

theorem step109wc132s2Dispatch :
    QuotientRankAtLeast (o132SourceU_wc ⟨2, by omega⟩) 14 := by
  have hP : Invertible (codeMat 465 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 279 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 465) (codeMat 279) o56W) 14 :=
    @quotientRankAtLeast_action (codeMat 465) (codeMat 279) hP hQ o56W 14
      step99_orbit56_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc132s2_contain hAct


private theorem step109wc132s3_QtInv :
    (codeMat 307 : Mat3).transpose⁻¹ = (codeMat 311 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 307 : Mat3).transpose * (codeMat 311 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc132s3_contain :
    (o132SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 337) (codeMat 307) o56W := by
  change spanCodes [304, 160, 84, 12, 2, 1] ≤ actionW (codeMat 337) (codeMat 307) o56W
  apply step109wc132_spanCodes_le_of_gens [304, 160, 84, 12, 2, 1]
    (actionW (codeMat 337) (codeMat 307) o56W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 430 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 430 (by decide)
    have hact : actionA (codeMat 337) (codeMat 307) (codeMat 430) = codeMat 304 := by
      unfold actionA
      rw [step109wc132s3_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 430 * (codeMat 311 : Mat3).transpose = codeMat 304
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 243 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 243 (by decide)
    have hact : actionA (codeMat 337) (codeMat 307) (codeMat 243) = codeMat 160 := by
      unfold actionA
      rw [step109wc132s3_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 243 * (codeMat 311 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 95 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 95 (by decide)
    have hact : actionA (codeMat 337) (codeMat 307) (codeMat 95) = codeMat 84 := by
      unfold actionA
      rw [step109wc132s3_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 95 * (codeMat 311 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 14 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 14 (by decide)
    have hact : actionA (codeMat 337) (codeMat 307) (codeMat 14) = codeMat 12 := by
      unfold actionA
      rw [step109wc132s3_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 14 * (codeMat 311 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 337) (codeMat 307) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [step109wc132s3_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 3 * (codeMat 311 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 337) (codeMat 307) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc132s3_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 1 * (codeMat 311 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact

theorem step109wc132s3Dispatch :
    QuotientRankAtLeast (o132SourceU_wc ⟨3, by omega⟩) 14 := by
  have hP : Invertible (codeMat 337 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 307 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 337) (codeMat 307) o56W) 14 :=
    @quotientRankAtLeast_action (codeMat 337) (codeMat 307) hP hQ o56W 14
      step99_orbit56_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc132s3_contain hAct


private theorem step109wc132s4_QtInv :
    (codeMat 314 : Mat3).transpose⁻¹ = (codeMat 271 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 314 : Mat3).transpose * (codeMat 271 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc132s4_contain :
    (o132SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 161) (codeMat 314) o57W_wc := by
  change spanCodes [304, 160, 100, 12, 2, 1] ≤ actionW (codeMat 161) (codeMat 314) o57W_wc
  apply step109wc132_spanCodes_le_of_gens [304, 160, 100, 12, 2, 1]
    (actionW (codeMat 161) (codeMat 314) o57W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 368 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 368 (by decide)
    have hact : actionA (codeMat 161) (codeMat 314) (codeMat 368) = codeMat 304 := by
      unfold actionA
      rw [step109wc132s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 368 * (codeMat 271 : Mat3).transpose = codeMat 304
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 408 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 408 (by decide)
    have hact : actionA (codeMat 161) (codeMat 314) (codeMat 408) = codeMat 160 := by
      unfold actionA
      rw [step109wc132s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 408 * (codeMat 271 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 406 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 406 (by decide)
    have hact : actionA (codeMat 161) (codeMat 314) (codeMat 406) = codeMat 100 := by
      unfold actionA
      rw [step109wc132s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 406 * (codeMat 271 : Mat3).transpose = codeMat 100
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 134 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 134 (by decide)
    have hact : actionA (codeMat 161) (codeMat 314) (codeMat 134) = codeMat 12 := by
      unfold actionA
      rw [step109wc132s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 134 * (codeMat 271 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 161) (codeMat 314) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [step109wc132s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 3 * (codeMat 271 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 314) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc132s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 271 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact

theorem step109wc132s4Dispatch :
    QuotientRankAtLeast (o132SourceU_wc ⟨4, by omega⟩) 14 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 314 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 314) o57W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 314) hP hQ o57W_wc 14
      step109_orbit57_lb14_wc
  exact quotientRankAtLeast_mono step109wc132s4_contain hAct


private theorem step109wc132s5_QtInv :
    (codeMat 286 : Mat3).transpose⁻¹ = (codeMat 303 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 286 : Mat3).transpose * (codeMat 303 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc132s5_contain :
    (o132SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 177) (codeMat 286) o57W_wc := by
  change spanCodes [304, 160, 112, 12, 2, 1] ≤ actionW (codeMat 177) (codeMat 286) o57W_wc
  apply step109wc132_spanCodes_le_of_gens [304, 160, 112, 12, 2, 1]
    (actionW (codeMat 177) (codeMat 286) o57W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 232 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 232 (by decide)
    have hact : actionA (codeMat 177) (codeMat 286) (codeMat 232) = codeMat 304 := by
      unfold actionA
      rw [step109wc132s5_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 232 * (codeMat 303 : Mat3).transpose = codeMat 304
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 408 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 408 (by decide)
    have hact : actionA (codeMat 177) (codeMat 286) (codeMat 408) = codeMat 160 := by
      unfold actionA
      rw [step109wc132s5_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 408 * (codeMat 303 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 272 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 272 (by decide)
    have hact : actionA (codeMat 177) (codeMat 286) (codeMat 272) = codeMat 112 := by
      unfold actionA
      rw [step109wc132s5_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 272 * (codeMat 303 : Mat3).transpose = codeMat 112
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 133 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 133 (by decide)
    have hact : actionA (codeMat 177) (codeMat 286) (codeMat 133) = codeMat 12 := by
      unfold actionA
      rw [step109wc132s5_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 133 * (codeMat 303 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 177) (codeMat 286) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [step109wc132s5_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 3 * (codeMat 303 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 177) (codeMat 286) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc132s5_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 2 * (codeMat 303 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact

theorem step109wc132s5Dispatch :
    QuotientRankAtLeast (o132SourceU_wc ⟨5, by omega⟩) 14 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 286 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 286) o57W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 286) hP hQ o57W_wc 14
      step109_orbit57_lb14_wc
  exact quotientRankAtLeast_mono step109wc132s5_contain hAct


private theorem step109wc132s6_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc132s6_contain :
    (o132SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 140) (codeMat 266) orbit10W := by
  change spanCodes [272, 128, 64, 32, 12, 2, 1] ≤ actionW (codeMat 140) (codeMat 266) orbit10W
  apply step109wc132_spanCodes_le_of_gens [272, 128, 64, 32, 12, 2, 1]
    (actionW (codeMat 140) (codeMat 266) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 68 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 140) (codeMat 266) (codeMat 68) = codeMat 272 := by
      unfold actionA
      rw [step109wc132s6_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 68 * (codeMat 266 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 140) (codeMat 266) (codeMat 1) = codeMat 128 := by
      unfold actionA
      rw [step109wc132s6_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 140) (codeMat 266) (codeMat 2) = codeMat 64 := by
      unfold actionA
      rw [step109wc132s6_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 2 * (codeMat 266 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 140) (codeMat 266) (codeMat 256) = codeMat 32 := by
      unfold actionA
      rw [step109wc132s6_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 256 * (codeMat 266 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 140) (codeMat 266) (codeMat 160) = codeMat 12 := by
      unfold actionA
      rw [step109wc132s6_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 160 * (codeMat 266 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 140) (codeMat 266) (codeMat 8) = codeMat 2 := by
      unfold actionA
      rw [step109wc132s6_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 8 * (codeMat 266 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 140) (codeMat 266) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc132s6_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 16 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact

theorem step109wc132s6Dispatch :
    QuotientRankAtLeast (o132SourceU_wc ⟨6, by omega⟩) 12 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 266) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 266) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc132s6_contain hAct


private theorem step109wc132s7_QtInv :
    (codeMat 270 : Mat3).transpose⁻¹ = (codeMat 298 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 270 : Mat3).transpose * (codeMat 298 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc132s7_contain :
    (o132SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 142) (codeMat 270) orbit10W := by
  change spanCodes [256, 144, 68, 48, 12, 2, 1] ≤ actionW (codeMat 142) (codeMat 270) orbit10W
  apply step109wc132_spanCodes_le_of_gens [256, 144, 68, 48, 12, 2, 1]
    (actionW (codeMat 142) (codeMat 270) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 325 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 325 (by decide)
    have hact : actionA (codeMat 142) (codeMat 270) (codeMat 325) = codeMat 256 := by
      unfold actionA
      rw [step109wc132s7_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 325 * (codeMat 298 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 142) (codeMat 270) (codeMat 1) = codeMat 144 := by
      unfold actionA
      rw [step109wc132s7_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 1 * (codeMat 298 : Mat3).transpose = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 170 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 170 (by decide)
    have hact : actionA (codeMat 142) (codeMat 270) (codeMat 170) = codeMat 68 := by
      unfold actionA
      rw [step109wc132s7_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 170 * (codeMat 298 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 142) (codeMat 270) (codeMat 256) = codeMat 48 := by
      unfold actionA
      rw [step109wc132s7_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 256 * (codeMat 298 : Mat3).transpose = codeMat 48
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 168 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 168 (by decide)
    have hact : actionA (codeMat 142) (codeMat 270) (codeMat 168) = codeMat 12 := by
      unfold actionA
      rw [step109wc132s7_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 168 * (codeMat 298 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 142) (codeMat 270) (codeMat 8) = codeMat 2 := by
      unfold actionA
      rw [step109wc132s7_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 8 * (codeMat 298 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 142) (codeMat 270) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc132s7_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 16 * (codeMat 298 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact

theorem step109wc132s7Dispatch :
    QuotientRankAtLeast (o132SourceU_wc ⟨7, by omega⟩) 12 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 270 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 270) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 270) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc132s7_contain hAct


private theorem step109wc132s8_QtInv :
    (codeMat 270 : Mat3).transpose⁻¹ = (codeMat 298 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 270 : Mat3).transpose * (codeMat 298 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc132s8_contain :
    (o132SourceU_wc ⟨8, by omega⟩) ≤ actionW (codeMat 273) (codeMat 270) flatW_7 := by
  change spanCodes [288, 160, 16, 8, 4, 2, 1] ≤ actionW (codeMat 273) (codeMat 270) flatW_7
  apply step109wc132_spanCodes_le_of_gens [288, 160, 16, 8, 4, 2, 1]
    (actionW (codeMat 273) (codeMat 270) flatW_7)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 360 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 360 (by decide)
    have hact : actionA (codeMat 273) (codeMat 270) (codeMat 360) = codeMat 288 := by
      unfold actionA
      rw [step109wc132s8_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 360 * (codeMat 298 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 104 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 104 (by decide)
    have hact : actionA (codeMat 273) (codeMat 270) (codeMat 104) = codeMat 160 := by
      unfold actionA
      rw [step109wc132s8_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 104 * (codeMat 298 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 270) (codeMat 8) = codeMat 16 := by
      unfold actionA
      rw [step109wc132s8_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 298 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 16 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 16 (by decide)
    have hact : actionA (codeMat 273) (codeMat 270) (codeMat 16) = codeMat 8 := by
      unfold actionA
      rw [step109wc132s8_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 16 * (codeMat 298 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 5 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 5 (by decide)
    have hact : actionA (codeMat 273) (codeMat 270) (codeMat 5) = codeMat 4 := by
      unfold actionA
      rw [step109wc132s8_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 5 * (codeMat 298 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 270) (codeMat 1) = codeMat 2 := by
      unfold actionA
      rw [step109wc132s8_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 298 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 270) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc132s8_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 298 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc132_codeMat_mem_actionW_of_witness hw hact

theorem step109wc132s8Dispatch :
    QuotientRankAtLeast (o132SourceU_wc ⟨8, by omega⟩) 9 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 270 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 270) flatW_7) 9 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 270) hP hQ flatW_7 9
      flatSeed_7
  exact quotientRankAtLeast_mono step109wc132s8_contain hAct

theorem step109wc132_all_dispatch (i : Fin 9) :
    QuotientRankAtLeast (o132SourceU_wc i) (o132SourceLb_wc i) := by
  fin_cases i
  · exact step109wc132s0Dispatch
  · exact step109wc132s1Dispatch
  · exact step109wc132s2Dispatch
  · exact step109wc132s3Dispatch
  · exact step109wc132s4Dispatch
  · exact step109wc132s5Dispatch
  · exact step109wc132s6Dispatch
  · exact step109wc132s7Dispatch
  · exact step109wc132s8Dispatch

theorem step109_orbit132_lb15_wc : QuotientRankAtLeast o132W_wc 15 :=
  o132Lb15_wc step109wc132_all_dispatch

end QiushiMatmul
