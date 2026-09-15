import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit147Consumer
import QiushiOrbit29FP
import QiushiWcOrbit64Dispatch
import QiushiStep99Orbit65Dispatch
import QiushiWcOrbit63Dispatch
import QiushiWcOrbit45Dispatch

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc147_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc147_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc147s0_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc147s0_contain :
    (o147SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 266) (codeMat 266) orbit29W := by
  change spanCodes [160, 68, 16, 8, 2, 1] ≤ actionW (codeMat 266) (codeMat 266) orbit29W
  apply step109wc147_spanCodes_le_of_gens [160, 68, 16, 8, 2, 1]
    (actionW (codeMat 266) (codeMat 266) orbit29W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 68 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 68 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 68) = codeMat 160 := by
      unfold actionA
      rw [step109wc147s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 68 * (codeMat 266 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 160 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 160) = codeMat 68 := by
      unfold actionA
      rw [step109wc147s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 160 * (codeMat 266 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step109wc147s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 2) = codeMat 8 := by
      unfold actionA
      rw [step109wc147s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 266 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 8) = codeMat 2 := by
      unfold actionA
      rw [step109wc147s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 266 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc147s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact

theorem step109wc147s0Dispatch :
    QuotientRankAtLeast (o147SourceU_wc ⟨0, by omega⟩) 15 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 266) orbit29W) 15 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 266) hP hQ orbit29W 15
      orbit29_lb15
  exact quotientRankAtLeast_mono step109wc147s0_contain hAct


private theorem step109wc147s1_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc147s1_contain :
    (o147SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 266) (codeMat 266) o64W_wc := by
  change spanCodes [258, 160, 68, 16, 10, 1] ≤ actionW (codeMat 266) (codeMat 266) o64W_wc
  apply step109wc147_spanCodes_le_of_gens [258, 160, 68, 16, 10, 1]
    (actionW (codeMat 266) (codeMat 266) o64W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 264 ∈ o64W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 68, 16, 10, 1] 264 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 264) = codeMat 258 := by
      unfold actionA
      rw [step109wc147s1_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 264 * (codeMat 266 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 68 ∈ o64W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 68, 16, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 68) = codeMat 160 := by
      unfold actionA
      rw [step109wc147s1_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 68 * (codeMat 266 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 160 ∈ o64W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 68, 16, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 160) = codeMat 68 := by
      unfold actionA
      rw [step109wc147s1_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 160 * (codeMat 266 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o64W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 68, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step109wc147s1_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 10 ∈ o64W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 68, 16, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step109wc147s1_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 10 * (codeMat 266 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ o64W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc147s1_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact

theorem step109wc147s1Dispatch :
    QuotientRankAtLeast (o147SourceU_wc ⟨1, by omega⟩) 15 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 266) o64W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 266) hP hQ o64W_wc 15
      step109_orbit64_lb15_wc
  exact quotientRankAtLeast_mono step109wc147s1_contain hAct


private theorem step109wc147s2_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc147s2_contain :
    (o147SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 273) (codeMat 273) o65W := by
  change spanCodes [260, 160, 68, 16, 10, 1] ≤ actionW (codeMat 273) (codeMat 273) o65W
  apply step109wc147_spanCodes_le_of_gens [260, 160, 68, 16, 10, 1]
    (actionW (codeMat 273) (codeMat 273) o65W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 260 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 260 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 260) = codeMat 260 := by
      unfold actionA
      rw [step109wc147s2_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 260 * (codeMat 273 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 160) = codeMat 160 := by
      unfold actionA
      rw [step109wc147s2_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 160 * (codeMat 273 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 68) = codeMat 68 := by
      unfold actionA
      rw [step109wc147s2_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 68 * (codeMat 273 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 16 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 16) = codeMat 16 := by
      unfold actionA
      rw [step109wc147s2_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 16 * (codeMat 273 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 10 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step109wc147s2_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 10 * (codeMat 273 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc147s2_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact

theorem step109wc147s2Dispatch :
    QuotientRankAtLeast (o147SourceU_wc ⟨2, by omega⟩) 15 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 273) o65W) 15 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 273) hP hQ o65W 15
      step99_orbit65_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc147s2_contain hAct


private theorem step109wc147s3_QtInv :
    (codeMat 305 : Mat3).transpose⁻¹ = (codeMat 305 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 305 : Mat3).transpose * (codeMat 305 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc147s3_contain :
    (o147SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 401) (codeMat 305) o65W := by
  change spanCodes [262, 160, 68, 16, 10, 1] ≤ actionW (codeMat 401) (codeMat 305) o65W
  apply step109wc147_spanCodes_le_of_gens [262, 160, 68, 16, 10, 1]
    (actionW (codeMat 401) (codeMat 305) o65W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 436 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 436 (by decide)
    have hact : actionA (codeMat 401) (codeMat 305) (codeMat 436) = codeMat 262 := by
      unfold actionA
      rw [step109wc147s3_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 436 * (codeMat 305 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 401) (codeMat 305) (codeMat 160) = codeMat 160 := by
      unfold actionA
      rw [step109wc147s3_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 160 * (codeMat 305 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 78 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 78 (by decide)
    have hact : actionA (codeMat 401) (codeMat 305) (codeMat 78) = codeMat 68 := by
      unfold actionA
      rw [step109wc147s3_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 78 * (codeMat 305 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 16 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 401) (codeMat 305) (codeMat 16) = codeMat 16 := by
      unfold actionA
      rw [step109wc147s3_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 16 * (codeMat 305 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 10 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 401) (codeMat 305) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step109wc147s3_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 10 * (codeMat 305 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 401) (codeMat 305) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc147s3_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 1 * (codeMat 305 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact

theorem step109wc147s3Dispatch :
    QuotientRankAtLeast (o147SourceU_wc ⟨3, by omega⟩) 15 := by
  have hP : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 401) (codeMat 305) o65W) 15 :=
    @quotientRankAtLeast_action (codeMat 401) (codeMat 305) hP hQ o65W 15
      step99_orbit65_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc147s3_contain hAct


private theorem step109wc147s4_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc147s4_contain :
    (o147SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 266) (codeMat 266) o65W := by
  change spanCodes [288, 160, 68, 16, 10, 1] ≤ actionW (codeMat 266) (codeMat 266) o65W
  apply step109wc147_spanCodes_le_of_gens [288, 160, 68, 16, 10, 1]
    (actionW (codeMat 266) (codeMat 266) o65W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 260 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 260 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 260) = codeMat 288 := by
      unfold actionA
      rw [step109wc147s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 260 * (codeMat 266 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 68 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 68) = codeMat 160 := by
      unfold actionA
      rw [step109wc147s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 68 * (codeMat 266 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 160 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 160) = codeMat 68 := by
      unfold actionA
      rw [step109wc147s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 160 * (codeMat 266 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step109wc147s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 10 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step109wc147s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 10 * (codeMat 266 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc147s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact

theorem step109wc147s4Dispatch :
    QuotientRankAtLeast (o147SourceU_wc ⟨4, by omega⟩) 15 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 266) o65W) 15 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 266) hP hQ o65W 15
      step99_orbit65_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc147s4_contain hAct


private theorem step109wc147s5_QtInv :
    (codeMat 298 : Mat3).transpose⁻¹ = (codeMat 270 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 298 : Mat3).transpose * (codeMat 270 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc147s5_contain :
    (o147SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 330) (codeMat 298) o65W := by
  change spanCodes [290, 160, 68, 16, 10, 1] ≤ actionW (codeMat 330) (codeMat 298) o65W
  apply step109wc147_spanCodes_le_of_gens [290, 160, 68, 16, 10, 1]
    (actionW (codeMat 330) (codeMat 298) o65W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 446 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 446 (by decide)
    have hact : actionA (codeMat 330) (codeMat 298) (codeMat 446) = codeMat 290 := by
      unfold actionA
      rw [step109wc147s5_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 446 * (codeMat 270 : Mat3).transpose = codeMat 290
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 78 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 78 (by decide)
    have hact : actionA (codeMat 330) (codeMat 298) (codeMat 78) = codeMat 160 := by
      unfold actionA
      rw [step109wc147s5_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 78 * (codeMat 270 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 160 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 330) (codeMat 298) (codeMat 160) = codeMat 68 := by
      unfold actionA
      rw [step109wc147s5_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 160 * (codeMat 270 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 330) (codeMat 298) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step109wc147s5_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 1 * (codeMat 270 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 10 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 330) (codeMat 298) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step109wc147s5_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 10 * (codeMat 270 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 330) (codeMat 298) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc147s5_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 16 * (codeMat 270 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact

theorem step109wc147s5Dispatch :
    QuotientRankAtLeast (o147SourceU_wc ⟨5, by omega⟩) 15 := by
  have hP : Invertible (codeMat 330 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 298 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 330) (codeMat 298) o65W) 15 :=
    @quotientRankAtLeast_action (codeMat 330) (codeMat 298) hP hQ o65W 15
      step99_orbit65_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc147s5_contain hAct


private theorem step109wc147s6_QtInv :
    (codeMat 282 : Mat3).transpose⁻¹ = (codeMat 267 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 282 : Mat3).transpose * (codeMat 267 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc147s6_contain :
    (o147SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 267) (codeMat 282) o65W := by
  change spanCodes [292, 160, 68, 16, 10, 1] ≤ actionW (codeMat 267) (codeMat 282) o65W
  apply step109wc147_spanCodes_le_of_gens [292, 160, 68, 16, 10, 1]
    (actionW (codeMat 267) (codeMat 282) o65W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 260 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 260 (by decide)
    have hact : actionA (codeMat 267) (codeMat 282) (codeMat 260) = codeMat 292 := by
      unfold actionA
      rw [step109wc147s6_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 260 * (codeMat 267 : Mat3).transpose = codeMat 292
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 228 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 228 (by decide)
    have hact : actionA (codeMat 267) (codeMat 282) (codeMat 228) = codeMat 160 := by
      unfold actionA
      rw [step109wc147s6_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 228 * (codeMat 267 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 160 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 267) (codeMat 282) (codeMat 160) = codeMat 68 := by
      unfold actionA
      rw [step109wc147s6_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 160 * (codeMat 267 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 27 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 27 (by decide)
    have hact : actionA (codeMat 267) (codeMat 282) (codeMat 27) = codeMat 16 := by
      unfold actionA
      rw [step109wc147s6_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 27 * (codeMat 267 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 10 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 267) (codeMat 282) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step109wc147s6_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 10 * (codeMat 267 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 267) (codeMat 282) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc147s6_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 16 * (codeMat 267 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact

theorem step109wc147s6Dispatch :
    QuotientRankAtLeast (o147SourceU_wc ⟨6, by omega⟩) 15 := by
  have hP : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 282 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 267) (codeMat 282) o65W) 15 :=
    @quotientRankAtLeast_action (codeMat 267) (codeMat 282) hP hQ o65W 15
      step99_orbit65_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc147s6_contain hAct


private theorem step109wc147s7_QtInv :
    (codeMat 314 : Mat3).transpose⁻¹ = (codeMat 271 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 314 : Mat3).transpose * (codeMat 271 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc147s7_contain :
    (o147SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 331) (codeMat 314) o65W := by
  change spanCodes [294, 160, 68, 16, 10, 1] ≤ actionW (codeMat 331) (codeMat 314) o65W
  apply step109wc147_spanCodes_le_of_gens [294, 160, 68, 16, 10, 1]
    (actionW (codeMat 331) (codeMat 314) o65W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 430 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 430 (by decide)
    have hact : actionA (codeMat 331) (codeMat 314) (codeMat 430) = codeMat 294 := by
      unfold actionA
      rw [step109wc147s7_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 430 * (codeMat 271 : Mat3).transpose = codeMat 294
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 238 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 238 (by decide)
    have hact : actionA (codeMat 331) (codeMat 314) (codeMat 238) = codeMat 160 := by
      unfold actionA
      rw [step109wc147s7_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 238 * (codeMat 271 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 160 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 331) (codeMat 314) (codeMat 160) = codeMat 68 := by
      unfold actionA
      rw [step109wc147s7_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 160 * (codeMat 271 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 27 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 27 (by decide)
    have hact : actionA (codeMat 331) (codeMat 314) (codeMat 27) = codeMat 16 := by
      unfold actionA
      rw [step109wc147s7_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 27 * (codeMat 271 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 10 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 331) (codeMat 314) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step109wc147s7_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 10 * (codeMat 271 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 331) (codeMat 314) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc147s7_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 16 * (codeMat 271 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact

theorem step109wc147s7Dispatch :
    QuotientRankAtLeast (o147SourceU_wc ⟨7, by omega⟩) 15 := by
  have hP : Invertible (codeMat 331 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 314 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 331) (codeMat 314) o65W) 15 :=
    @quotientRankAtLeast_action (codeMat 331) (codeMat 314) hP hQ o65W 15
      step99_orbit65_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc147s7_contain hAct


private theorem step109wc147s8_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc147s8_contain :
    (o147SourceU_wc ⟨8, by omega⟩) ≤ actionW (codeMat 84) (codeMat 84) o63W_wc := by
  change spanCodes [256, 160, 68, 16, 10, 1] ≤ actionW (codeMat 84) (codeMat 84) o63W_wc
  apply step109wc147_spanCodes_le_of_gens [256, 160, 68, 16, 10, 1]
    (actionW (codeMat 84) (codeMat 84) o63W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 1 ∈ o63W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step109wc147s8_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 84 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 10 ∈ o63W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 16, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 10) = codeMat 160 := by
      unfold actionA
      rw [step109wc147s8_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 10 * (codeMat 84 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ o63W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 16, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 68) = codeMat 68 := by
      unfold actionA
      rw [step109wc147s8_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 68 * (codeMat 84 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 16 ∈ o63W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 16) = codeMat 16 := by
      unfold actionA
      rw [step109wc147s8_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 16 * (codeMat 84 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 160 ∈ o63W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 16, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step109wc147s8_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 160 * (codeMat 84 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 256 ∈ o63W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 16, 10, 1] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc147s8_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 84 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact

theorem step109wc147s8Dispatch :
    QuotientRankAtLeast (o147SourceU_wc ⟨8, by omega⟩) 14 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 84) o63W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 84) hP hQ o63W_wc 14
      step109_orbit63_lb14_wc
  exact quotientRankAtLeast_mono step109wc147s8_contain hAct


private theorem step109wc147s9_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc147s9_contain :
    (o147SourceU_wc ⟨9, by omega⟩) ≤ actionW (codeMat 161) (codeMat 161) o45W_wc := by
  change spanCodes [160, 64, 16, 10, 4, 1] ≤ actionW (codeMat 161) (codeMat 161) o45W_wc
  apply step109wc147_spanCodes_le_of_gens [160, 64, 16, 10, 4, 1]
    (actionW (codeMat 161) (codeMat 161) o45W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 160 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 160) = codeMat 160 := by
      unfold actionA
      rw [step109wc147s9_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * (codeMat 161 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 8 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 8) = codeMat 64 := by
      unfold actionA
      rw [step109wc147s9_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 8 * (codeMat 161 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 256 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 256) = codeMat 16 := by
      unfold actionA
      rw [step109wc147s9_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 256 * (codeMat 161 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 68 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 68 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 68) = codeMat 10 := by
      unfold actionA
      rw [step109wc147s9_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 68 * (codeMat 161 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 2) = codeMat 4 := by
      unfold actionA
      rw [step109wc147s9_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 161 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc147s9_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact

theorem step109wc147s9Dispatch :
    QuotientRankAtLeast (o147SourceU_wc ⟨9, by omega⟩) 13 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 161) o45W_wc) 13 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 161) hP hQ o45W_wc 13
      step109_orbit45_lb13_wc
  exact quotientRankAtLeast_mono step109wc147s9_contain hAct


private theorem step109wc147s10_QtInv :
    (codeMat 417 : Mat3).transpose⁻¹ = (codeMat 177 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 417 : Mat3).transpose * (codeMat 177 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc147s10_contain :
    (o147SourceU_wc ⟨10, by omega⟩) ≤ actionW (codeMat 177) (codeMat 417) o45W_wc := by
  change spanCodes [160, 66, 16, 10, 6, 1] ≤ actionW (codeMat 177) (codeMat 417) o45W_wc
  apply step109wc147_spanCodes_le_of_gens [160, 66, 16, 10, 6, 1]
    (actionW (codeMat 177) (codeMat 417) o45W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 160 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 160 (by decide)
    have hact : actionA (codeMat 177) (codeMat 417) (codeMat 160) = codeMat 160 := by
      unfold actionA
      rw [step109wc147s10_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 160 * (codeMat 177 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 76 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 76 (by decide)
    have hact : actionA (codeMat 177) (codeMat 417) (codeMat 76) = codeMat 66 := by
      unfold actionA
      rw [step109wc147s10_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 76 * (codeMat 177 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 256 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 177) (codeMat 417) (codeMat 256) = codeMat 16 := by
      unfold actionA
      rw [step109wc147s10_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 256 * (codeMat 177 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 68 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 68 (by decide)
    have hact : actionA (codeMat 177) (codeMat 417) (codeMat 68) = codeMat 10 := by
      unfold actionA
      rw [step109wc147s10_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 68 * (codeMat 177 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 177) (codeMat 417) (codeMat 2) = codeMat 6 := by
      unfold actionA
      rw [step109wc147s10_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 2 * (codeMat 177 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 417) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc147s10_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * (codeMat 177 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact

theorem step109wc147s10Dispatch :
    QuotientRankAtLeast (o147SourceU_wc ⟨10, by omega⟩) 13 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 417) o45W_wc) 13 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 417) hP hQ o45W_wc 13
      step109_orbit45_lb13_wc
  exact quotientRankAtLeast_mono step109wc147s10_contain hAct


private theorem step109wc147s11_QtInv :
    (codeMat 98 : Mat3).transpose⁻¹ = (codeMat 140 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 98 : Mat3).transpose * (codeMat 140 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc147s11_contain :
    (o147SourceU_wc ⟨11, by omega⟩) ≤ actionW (codeMat 98) (codeMat 98) o45W_wc := by
  change spanCodes [128, 68, 32, 16, 10, 1] ≤ actionW (codeMat 98) (codeMat 98) o45W_wc
  apply step109wc147_spanCodes_le_of_gens [128, 68, 32, 16, 10, 1]
    (actionW (codeMat 98) (codeMat 98) o45W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 8 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 98) (codeMat 98) (codeMat 8) = codeMat 128 := by
      unfold actionA
      rw [step109wc147s11_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 8 * (codeMat 140 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 160 (by decide)
    have hact : actionA (codeMat 98) (codeMat 98) (codeMat 160) = codeMat 68 := by
      unfold actionA
      rw [step109wc147s11_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 160 * (codeMat 140 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 98) (codeMat 98) (codeMat 2) = codeMat 32 := by
      unfold actionA
      rw [step109wc147s11_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 2 * (codeMat 140 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 98) (codeMat 98) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step109wc147s11_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 1 * (codeMat 140 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 68 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 68 (by decide)
    have hact : actionA (codeMat 98) (codeMat 98) (codeMat 68) = codeMat 10 := by
      unfold actionA
      rw [step109wc147s11_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 68 * (codeMat 140 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 256 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 98) (codeMat 98) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc147s11_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 256 * (codeMat 140 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact

theorem step109wc147s11Dispatch :
    QuotientRankAtLeast (o147SourceU_wc ⟨11, by omega⟩) 13 := by
  have hP : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 98) (codeMat 98) o45W_wc) 13 :=
    @quotientRankAtLeast_action (codeMat 98) (codeMat 98) hP hQ o45W_wc 13
      step109_orbit45_lb13_wc
  exact quotientRankAtLeast_mono step109wc147s11_contain hAct


private theorem step109wc147s12_QtInv :
    (codeMat 354 : Mat3).transpose⁻¹ = (codeMat 142 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 354 : Mat3).transpose * (codeMat 142 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc147s12_contain :
    (o147SourceU_wc ⟨12, by omega⟩) ≤ actionW (codeMat 106) (codeMat 354) o45W_wc := by
  change spanCodes [130, 68, 34, 16, 10, 1] ≤ actionW (codeMat 106) (codeMat 354) o45W_wc
  apply step109wc147_spanCodes_le_of_gens [130, 68, 34, 16, 10, 1]
    (actionW (codeMat 106) (codeMat 354) o45W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 8 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 106) (codeMat 354) (codeMat 8) = codeMat 130 := by
      unfold actionA
      rw [step109wc147s12_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 8 * (codeMat 142 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 160 (by decide)
    have hact : actionA (codeMat 106) (codeMat 354) (codeMat 160) = codeMat 68 := by
      unfold actionA
      rw [step109wc147s12_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 160 * (codeMat 142 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 70 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 70 (by decide)
    have hact : actionA (codeMat 106) (codeMat 354) (codeMat 70) = codeMat 34 := by
      unfold actionA
      rw [step109wc147s12_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 70 * (codeMat 142 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 106) (codeMat 354) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step109wc147s12_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 1 * (codeMat 142 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 68 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 68 (by decide)
    have hact : actionA (codeMat 106) (codeMat 354) (codeMat 68) = codeMat 10 := by
      unfold actionA
      rw [step109wc147s12_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 68 * (codeMat 142 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 256 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 106) (codeMat 354) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc147s12_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 256 * (codeMat 142 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact

theorem step109wc147s12Dispatch :
    QuotientRankAtLeast (o147SourceU_wc ⟨12, by omega⟩) 13 := by
  have hP : Invertible (codeMat 106 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 354 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 106) (codeMat 354) o45W_wc) 13 :=
    @quotientRankAtLeast_action (codeMat 106) (codeMat 354) hP hQ o45W_wc 13
      step109_orbit45_lb13_wc
  exact quotientRankAtLeast_mono step109wc147s12_contain hAct


private theorem step109wc147s13_QtInv :
    (codeMat 226 : Mat3).transpose⁻¹ = (codeMat 141 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 226 : Mat3).transpose * (codeMat 141 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc147s13_contain :
    (o147SourceU_wc ⟨13, by omega⟩) ≤ actionW (codeMat 99) (codeMat 226) o45W_wc := by
  change spanCodes [132, 68, 36, 16, 10, 1] ≤ actionW (codeMat 99) (codeMat 226) o45W_wc
  apply step109wc147_spanCodes_le_of_gens [132, 68, 36, 16, 10, 1]
    (actionW (codeMat 99) (codeMat 226) o45W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 168 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 168 (by decide)
    have hact : actionA (codeMat 99) (codeMat 226) (codeMat 168) = codeMat 132 := by
      unfold actionA
      rw [step109wc147s13_QtInv]
      show (codeMat 99 : Mat3).transpose * codeMat 168 * (codeMat 141 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 160 (by decide)
    have hact : actionA (codeMat 99) (codeMat 226) (codeMat 160) = codeMat 68 := by
      unfold actionA
      rw [step109wc147s13_QtInv]
      show (codeMat 99 : Mat3).transpose * codeMat 160 * (codeMat 141 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 99) (codeMat 226) (codeMat 2) = codeMat 36 := by
      unfold actionA
      rw [step109wc147s13_QtInv]
      show (codeMat 99 : Mat3).transpose * codeMat 2 * (codeMat 141 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 325 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 325 (by decide)
    have hact : actionA (codeMat 99) (codeMat 226) (codeMat 325) = codeMat 16 := by
      unfold actionA
      rw [step109wc147s13_QtInv]
      show (codeMat 99 : Mat3).transpose * codeMat 325 * (codeMat 141 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 68 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 68 (by decide)
    have hact : actionA (codeMat 99) (codeMat 226) (codeMat 68) = codeMat 10 := by
      unfold actionA
      rw [step109wc147s13_QtInv]
      show (codeMat 99 : Mat3).transpose * codeMat 68 * (codeMat 141 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 256 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 99) (codeMat 226) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc147s13_QtInv]
      show (codeMat 99 : Mat3).transpose * codeMat 256 * (codeMat 141 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact

theorem step109wc147s13Dispatch :
    QuotientRankAtLeast (o147SourceU_wc ⟨13, by omega⟩) 13 := by
  have hP : Invertible (codeMat 99 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 226 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 99) (codeMat 226) o45W_wc) 13 :=
    @quotientRankAtLeast_action (codeMat 99) (codeMat 226) hP hQ o45W_wc 13
      step109_orbit45_lb13_wc
  exact quotientRankAtLeast_mono step109wc147s13_contain hAct


private theorem step109wc147s14_QtInv :
    (codeMat 482 : Mat3).transpose⁻¹ = (codeMat 143 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 482 : Mat3).transpose * (codeMat 143 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc147s14_contain :
    (o147SourceU_wc ⟨14, by omega⟩) ≤ actionW (codeMat 107) (codeMat 482) o45W_wc := by
  change spanCodes [134, 68, 38, 16, 10, 1] ≤ actionW (codeMat 107) (codeMat 482) o45W_wc
  apply step109wc147_spanCodes_le_of_gens [134, 68, 38, 16, 10, 1]
    (actionW (codeMat 107) (codeMat 482) o45W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 424 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 424 (by decide)
    have hact : actionA (codeMat 107) (codeMat 482) (codeMat 424) = codeMat 134 := by
      unfold actionA
      rw [step109wc147s14_QtInv]
      show (codeMat 107 : Mat3).transpose * codeMat 424 * (codeMat 143 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 160 (by decide)
    have hact : actionA (codeMat 107) (codeMat 482) (codeMat 160) = codeMat 68 := by
      unfold actionA
      rw [step109wc147s14_QtInv]
      show (codeMat 107 : Mat3).transpose * codeMat 160 * (codeMat 143 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 326 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 326 (by decide)
    have hact : actionA (codeMat 107) (codeMat 482) (codeMat 326) = codeMat 38 := by
      unfold actionA
      rw [step109wc147s14_QtInv]
      show (codeMat 107 : Mat3).transpose * codeMat 326 * (codeMat 143 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 325 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 325 (by decide)
    have hact : actionA (codeMat 107) (codeMat 482) (codeMat 325) = codeMat 16 := by
      unfold actionA
      rw [step109wc147s14_QtInv]
      show (codeMat 107 : Mat3).transpose * codeMat 325 * (codeMat 143 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 68 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 68 (by decide)
    have hact : actionA (codeMat 107) (codeMat 482) (codeMat 68) = codeMat 10 := by
      unfold actionA
      rw [step109wc147s14_QtInv]
      show (codeMat 107 : Mat3).transpose * codeMat 68 * (codeMat 143 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 256 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 107) (codeMat 482) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc147s14_QtInv]
      show (codeMat 107 : Mat3).transpose * codeMat 256 * (codeMat 143 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc147_codeMat_mem_actionW_of_witness hw hact

theorem step109wc147s14Dispatch :
    QuotientRankAtLeast (o147SourceU_wc ⟨14, by omega⟩) 13 := by
  have hP : Invertible (codeMat 107 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 482 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 107) (codeMat 482) o45W_wc) 13 :=
    @quotientRankAtLeast_action (codeMat 107) (codeMat 482) hP hQ o45W_wc 13
      step109_orbit45_lb13_wc
  exact quotientRankAtLeast_mono step109wc147s14_contain hAct

theorem step109wc147_all_dispatch (i : Fin 15) :
    QuotientRankAtLeast (o147SourceU_wc i) (o147SourceLb_wc i) := by
  fin_cases i
  · exact step109wc147s0Dispatch
  · exact step109wc147s1Dispatch
  · exact step109wc147s2Dispatch
  · exact step109wc147s3Dispatch
  · exact step109wc147s4Dispatch
  · exact step109wc147s5Dispatch
  · exact step109wc147s6Dispatch
  · exact step109wc147s7Dispatch
  · exact step109wc147s8Dispatch
  · exact step109wc147s9Dispatch
  · exact step109wc147s10Dispatch
  · exact step109wc147s11Dispatch
  · exact step109wc147s12Dispatch
  · exact step109wc147s13Dispatch
  · exact step109wc147s14Dispatch

theorem step109_orbit147_lb16_wc : QuotientRankAtLeast o147W_wc 16 :=
  o147Lb16_wc step109wc147_all_dispatch

end QiushiMatmul
