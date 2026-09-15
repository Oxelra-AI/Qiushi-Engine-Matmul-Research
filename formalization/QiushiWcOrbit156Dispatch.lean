import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiWcOrbit156Consumer
import QiushiOrbit31FP
import QiushiWcOrbit72Dispatch
import QiushiMonoOrbit71From17
import QiushiStep99Orbit55Dispatch
import QiushiStep99Mono3032

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc156_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc156_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc156s0_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc156s0_contain :
    (o156SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 266) (codeMat 161) orbit31W := by
  change spanCodes [68, 32, 20, 8, 2, 1] ≤ actionW (codeMat 266) (codeMat 161) orbit31W
  apply step109wc156_spanCodes_le_of_gens [68, 32, 20, 8, 2, 1]
    (actionW (codeMat 266) (codeMat 161) orbit31W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 80 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 80 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 80) = codeMat 68 := by
      unfold actionA
      rw [step109wc156s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 80 * (codeMat 161 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 2) = codeMat 32 := by
      unfold actionA
      rw [step109wc156s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 161 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 20 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 20 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 20) = codeMat 20 := by
      unfold actionA
      rw [step109wc156s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 20 * (codeMat 161 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 1) = codeMat 8 := by
      unfold actionA
      rw [step109wc156s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 32 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 32 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 32) = codeMat 2 := by
      unfold actionA
      rw [step109wc156s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 161 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc156s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact

theorem step109wc156s0Dispatch :
    QuotientRankAtLeast (o156SourceU_wc ⟨0, by omega⟩) 15 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 161) orbit31W) 15 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 161) hP hQ orbit31W 15
      orbit31_lb15
  exact quotientRankAtLeast_mono step109wc156s0_contain hAct


private theorem step109wc156s1_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc156s1_contain :
    (o156SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 266) (codeMat 84) o72W_wc := by
  change spanCodes [258, 68, 32, 20, 10, 1] ≤ actionW (codeMat 266) (codeMat 84) o72W_wc
  apply step109wc156_spanCodes_le_of_gens [258, 68, 32, 20, 10, 1]
    (actionW (codeMat 266) (codeMat 84) o72W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 80 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 80 (by decide)
    have hact : actionA (codeMat 266) (codeMat 84) (codeMat 80) = codeMat 258 := by
      unfold actionA
      rw [step109wc156s1_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 80 * (codeMat 84 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 264 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 264 (by decide)
    have hact : actionA (codeMat 266) (codeMat 84) (codeMat 264) = codeMat 68 := by
      unfold actionA
      rw [step109wc156s1_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 264 * (codeMat 84 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 84) (codeMat 1) = codeMat 32 := by
      unfold actionA
      rw [step109wc156s1_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 84 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 10 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 266) (codeMat 84) (codeMat 10) = codeMat 20 := by
      unfold actionA
      rw [step109wc156s1_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 10 * (codeMat 84 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 20 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 20 (by decide)
    have hact : actionA (codeMat 266) (codeMat 84) (codeMat 20) = codeMat 10 := by
      unfold actionA
      rw [step109wc156s1_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 20 * (codeMat 84 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 266) (codeMat 84) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step109wc156s1_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 84 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact

theorem step109wc156s1Dispatch :
    QuotientRankAtLeast (o156SourceU_wc ⟨1, by omega⟩) 15 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 84) o72W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 84) hP hQ o72W_wc 15
      step109_orbit72_lb15_wc
  exact quotientRankAtLeast_mono step109wc156s1_contain hAct


private theorem step109wc156s2_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc156s2_contain :
    (o156SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 330) (codeMat 84) o72W_wc := by
  change spanCodes [262, 68, 32, 20, 10, 1] ≤ actionW (codeMat 330) (codeMat 84) o72W_wc
  apply step109wc156_spanCodes_le_of_gens [262, 68, 32, 20, 10, 1]
    (actionW (codeMat 330) (codeMat 84) o72W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 80 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 80 (by decide)
    have hact : actionA (codeMat 330) (codeMat 84) (codeMat 80) = codeMat 262 := by
      unfold actionA
      rw [step109wc156s2_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 80 * (codeMat 84 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 296 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 296 (by decide)
    have hact : actionA (codeMat 330) (codeMat 84) (codeMat 296) = codeMat 68 := by
      unfold actionA
      rw [step109wc156s2_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 296 * (codeMat 84 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 330) (codeMat 84) (codeMat 1) = codeMat 32 := by
      unfold actionA
      rw [step109wc156s2_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 1 * (codeMat 84 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 10 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 330) (codeMat 84) (codeMat 10) = codeMat 20 := by
      unfold actionA
      rw [step109wc156s2_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 10 * (codeMat 84 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 20 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 20 (by decide)
    have hact : actionA (codeMat 330) (codeMat 84) (codeMat 20) = codeMat 10 := by
      unfold actionA
      rw [step109wc156s2_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 20 * (codeMat 84 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 330) (codeMat 84) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step109wc156s2_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 32 * (codeMat 84 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact

theorem step109wc156s2Dispatch :
    QuotientRankAtLeast (o156SourceU_wc ⟨2, by omega⟩) 15 := by
  have hP : Invertible (codeMat 330 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 330) (codeMat 84) o72W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 330) (codeMat 84) hP hQ o72W_wc 15
      step109_orbit72_lb15_wc
  exact quotientRankAtLeast_mono step109wc156s2_contain hAct


private theorem step109wc156s3_QtInv :
    (codeMat 372 : Mat3).transpose⁻¹ = (codeMat 93 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 372 : Mat3).transpose * (codeMat 93 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc156s3_contain :
    (o156SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 395) (codeMat 372) o72W_wc := by
  change spanCodes [384, 68, 32, 20, 10, 1] ≤ actionW (codeMat 395) (codeMat 372) o72W_wc
  apply step109wc156_spanCodes_le_of_gens [384, 68, 32, 20, 10, 1]
    (actionW (codeMat 395) (codeMat 372) o72W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 365 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 365 (by decide)
    have hact : actionA (codeMat 395) (codeMat 372) (codeMat 365) = codeMat 384 := by
      unfold actionA
      rw [step109wc156s3_QtInv]
      show (codeMat 395 : Mat3).transpose * codeMat 365 * (codeMat 93 : Mat3).transpose = codeMat 384
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 284 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 284 (by decide)
    have hact : actionA (codeMat 395) (codeMat 372) (codeMat 284) = codeMat 68 := by
      unfold actionA
      rw [step109wc156s3_QtInv]
      show (codeMat 395 : Mat3).transpose * codeMat 284 * (codeMat 93 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 63 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 63 (by decide)
    have hact : actionA (codeMat 395) (codeMat 372) (codeMat 63) = codeMat 32 := by
      unfold actionA
      rw [step109wc156s3_QtInv]
      show (codeMat 395 : Mat3).transpose * codeMat 63 * (codeMat 93 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 42 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 42 (by decide)
    have hact : actionA (codeMat 395) (codeMat 372) (codeMat 42) = codeMat 20 := by
      unfold actionA
      rw [step109wc156s3_QtInv]
      show (codeMat 395 : Mat3).transpose * codeMat 42 * (codeMat 93 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 52 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 52 (by decide)
    have hact : actionA (codeMat 395) (codeMat 372) (codeMat 52) = codeMat 10 := by
      unfold actionA
      rw [step109wc156s3_QtInv]
      show (codeMat 395 : Mat3).transpose * codeMat 52 * (codeMat 93 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 395) (codeMat 372) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step109wc156s3_QtInv]
      show (codeMat 395 : Mat3).transpose * codeMat 32 * (codeMat 93 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact

theorem step109wc156s3Dispatch :
    QuotientRankAtLeast (o156SourceU_wc ⟨3, by omega⟩) 15 := by
  have hP : Invertible (codeMat 395 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 372 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 395) (codeMat 372) o72W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 395) (codeMat 372) hP hQ o72W_wc 15
      step109_orbit72_lb15_wc
  exact quotientRankAtLeast_mono step109wc156s3_contain hAct


private theorem step109wc156s4_QtInv :
    (codeMat 372 : Mat3).transpose⁻¹ = (codeMat 93 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 372 : Mat3).transpose * (codeMat 93 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc156s4_contain :
    (o156SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 459) (codeMat 372) o72W_wc := by
  change spanCodes [390, 68, 32, 20, 10, 1] ≤ actionW (codeMat 459) (codeMat 372) o72W_wc
  apply step109wc156_spanCodes_le_of_gens [390, 68, 32, 20, 10, 1]
    (actionW (codeMat 459) (codeMat 372) o72W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 365 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 365 (by decide)
    have hact : actionA (codeMat 459) (codeMat 372) (codeMat 365) = codeMat 390 := by
      unfold actionA
      rw [step109wc156s4_QtInv]
      show (codeMat 459 : Mat3).transpose * codeMat 365 * (codeMat 93 : Mat3).transpose = codeMat 390
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 316 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 316 (by decide)
    have hact : actionA (codeMat 459) (codeMat 372) (codeMat 316) = codeMat 68 := by
      unfold actionA
      rw [step109wc156s4_QtInv]
      show (codeMat 459 : Mat3).transpose * codeMat 316 * (codeMat 93 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 63 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 63 (by decide)
    have hact : actionA (codeMat 459) (codeMat 372) (codeMat 63) = codeMat 32 := by
      unfold actionA
      rw [step109wc156s4_QtInv]
      show (codeMat 459 : Mat3).transpose * codeMat 63 * (codeMat 93 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 42 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 42 (by decide)
    have hact : actionA (codeMat 459) (codeMat 372) (codeMat 42) = codeMat 20 := by
      unfold actionA
      rw [step109wc156s4_QtInv]
      show (codeMat 459 : Mat3).transpose * codeMat 42 * (codeMat 93 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 52 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 52 (by decide)
    have hact : actionA (codeMat 459) (codeMat 372) (codeMat 52) = codeMat 10 := by
      unfold actionA
      rw [step109wc156s4_QtInv]
      show (codeMat 459 : Mat3).transpose * codeMat 52 * (codeMat 93 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 459) (codeMat 372) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step109wc156s4_QtInv]
      show (codeMat 459 : Mat3).transpose * codeMat 32 * (codeMat 93 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact

theorem step109wc156s4Dispatch :
    QuotientRankAtLeast (o156SourceU_wc ⟨4, by omega⟩) 15 := by
  have hP : Invertible (codeMat 459 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 372 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 459) (codeMat 372) o72W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 459) (codeMat 372) hP hQ o72W_wc 15
      step109_orbit72_lb15_wc
  exact quotientRankAtLeast_mono step109wc156s4_contain hAct


private theorem step109wc156s5_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc156s5_contain :
    (o156SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 273) (codeMat 273) o71W_mono := by
  change spanCodes [128, 68, 32, 20, 10, 1] ≤ actionW (codeMat 273) (codeMat 273) o71W_mono
  apply step109wc156_spanCodes_le_of_gens [128, 68, 32, 20, 10, 1]
    (actionW (codeMat 273) (codeMat 273) o71W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 128 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 128) = codeMat 128 := by
      unfold actionA
      rw [step109wc156s5_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 128 * (codeMat 273 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 68 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 68) = codeMat 68 := by
      unfold actionA
      rw [step109wc156s5_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 68 * (codeMat 273 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 32 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 32) = codeMat 32 := by
      unfold actionA
      rw [step109wc156s5_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 32 * (codeMat 273 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 20 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 20 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 20) = codeMat 20 := by
      unfold actionA
      rw [step109wc156s5_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 20 * (codeMat 273 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 10 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step109wc156s5_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 10 * (codeMat 273 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc156s5_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact

theorem step109wc156s5Dispatch :
    QuotientRankAtLeast (o156SourceU_wc ⟨5, by omega⟩) 14 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 273) o71W_mono) 14 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 273) hP hQ o71W_mono 14
      orbit71_lb14_mono
  exact quotientRankAtLeast_mono step109wc156s5_contain hAct


private theorem step109wc156s6_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc156s6_contain :
    (o156SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 337) (codeMat 273) o71W_mono := by
  change spanCodes [130, 68, 32, 20, 10, 1] ≤ actionW (codeMat 337) (codeMat 273) o71W_mono
  apply step109wc156_spanCodes_le_of_gens [130, 68, 32, 20, 10, 1]
    (actionW (codeMat 337) (codeMat 273) o71W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 128 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 337) (codeMat 273) (codeMat 128) = codeMat 130 := by
      unfold actionA
      rw [step109wc156s6_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 128 * (codeMat 273 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 69 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 69 (by decide)
    have hact : actionA (codeMat 337) (codeMat 273) (codeMat 69) = codeMat 68 := by
      unfold actionA
      rw [step109wc156s6_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 69 * (codeMat 273 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 32 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 337) (codeMat 273) (codeMat 32) = codeMat 32 := by
      unfold actionA
      rw [step109wc156s6_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 32 * (codeMat 273 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 20 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 20 (by decide)
    have hact : actionA (codeMat 337) (codeMat 273) (codeMat 20) = codeMat 20 := by
      unfold actionA
      rw [step109wc156s6_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 20 * (codeMat 273 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 10 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 337) (codeMat 273) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step109wc156s6_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 10 * (codeMat 273 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 337) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc156s6_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact

theorem step109wc156s6Dispatch :
    QuotientRankAtLeast (o156SourceU_wc ⟨6, by omega⟩) 14 := by
  have hP : Invertible (codeMat 337 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 337) (codeMat 273) o71W_mono) 14 :=
    @quotientRankAtLeast_action (codeMat 337) (codeMat 273) hP hQ o71W_mono 14
      orbit71_lb14_mono
  exact quotientRankAtLeast_mono step109wc156s6_contain hAct


private theorem step109wc156s7_QtInv :
    (codeMat 309 : Mat3).transpose⁻¹ = (codeMat 309 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 309 : Mat3).transpose * (codeMat 309 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc156s7_contain :
    (o156SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 409) (codeMat 309) o71W_mono := by
  change spanCodes [132, 68, 32, 20, 10, 1] ≤ actionW (codeMat 409) (codeMat 309) o71W_mono
  apply step109wc156_spanCodes_le_of_gens [132, 68, 32, 20, 10, 1]
    (actionW (codeMat 409) (codeMat 309) o71W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 149 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 149 (by decide)
    have hact : actionA (codeMat 409) (codeMat 309) (codeMat 149) = codeMat 132 := by
      unfold actionA
      rw [step109wc156s7_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 149 * (codeMat 309 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 78 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 78 (by decide)
    have hact : actionA (codeMat 409) (codeMat 309) (codeMat 78) = codeMat 68 := by
      unfold actionA
      rw [step109wc156s7_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 78 * (codeMat 309 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 63 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 63 (by decide)
    have hact : actionA (codeMat 409) (codeMat 309) (codeMat 63) = codeMat 32 := by
      unfold actionA
      rw [step109wc156s7_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 63 * (codeMat 309 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 21 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 21 (by decide)
    have hact : actionA (codeMat 409) (codeMat 309) (codeMat 21) = codeMat 20 := by
      unfold actionA
      rw [step109wc156s7_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 21 * (codeMat 309 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 11 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 409) (codeMat 309) (codeMat 11) = codeMat 10 := by
      unfold actionA
      rw [step109wc156s7_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 11 * (codeMat 309 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 409) (codeMat 309) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc156s7_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 1 * (codeMat 309 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact

theorem step109wc156s7Dispatch :
    QuotientRankAtLeast (o156SourceU_wc ⟨7, by omega⟩) 14 := by
  have hP : Invertible (codeMat 409 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 309 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 409) (codeMat 309) o71W_mono) 14 :=
    @quotientRankAtLeast_action (codeMat 409) (codeMat 309) hP hQ o71W_mono 14
      orbit71_lb14_mono
  exact quotientRankAtLeast_mono step109wc156s7_contain hAct


private theorem step109wc156s8_QtInv :
    (codeMat 309 : Mat3).transpose⁻¹ = (codeMat 309 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 309 : Mat3).transpose * (codeMat 309 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc156s8_contain :
    (o156SourceU_wc ⟨8, by omega⟩) ≤ actionW (codeMat 473) (codeMat 309) o71W_mono := by
  change spanCodes [134, 68, 32, 20, 10, 1] ≤ actionW (codeMat 473) (codeMat 309) o71W_mono
  apply step109wc156_spanCodes_le_of_gens [134, 68, 32, 20, 10, 1]
    (actionW (codeMat 473) (codeMat 309) o71W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 149 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 149 (by decide)
    have hact : actionA (codeMat 473) (codeMat 309) (codeMat 149) = codeMat 134 := by
      unfold actionA
      rw [step109wc156s8_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 149 * (codeMat 309 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 79 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 79 (by decide)
    have hact : actionA (codeMat 473) (codeMat 309) (codeMat 79) = codeMat 68 := by
      unfold actionA
      rw [step109wc156s8_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 79 * (codeMat 309 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 63 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 63 (by decide)
    have hact : actionA (codeMat 473) (codeMat 309) (codeMat 63) = codeMat 32 := by
      unfold actionA
      rw [step109wc156s8_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 63 * (codeMat 309 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 21 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 21 (by decide)
    have hact : actionA (codeMat 473) (codeMat 309) (codeMat 21) = codeMat 20 := by
      unfold actionA
      rw [step109wc156s8_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 21 * (codeMat 309 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 11 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 473) (codeMat 309) (codeMat 11) = codeMat 10 := by
      unfold actionA
      rw [step109wc156s8_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 11 * (codeMat 309 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 473) (codeMat 309) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc156s8_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 1 * (codeMat 309 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact

theorem step109wc156s8Dispatch :
    QuotientRankAtLeast (o156SourceU_wc ⟨8, by omega⟩) 14 := by
  have hP : Invertible (codeMat 473 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 309 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 473) (codeMat 309) o71W_mono) 14 :=
    @quotientRankAtLeast_action (codeMat 473) (codeMat 309) hP hQ o71W_mono 14
      orbit71_lb14_mono
  exact quotientRankAtLeast_mono step109wc156s8_contain hAct

private def step109wc156s9SrcT : Submodule F2 Mat3 := spanCodes [272, 128, 66, 34, 8, 1]

private theorem step109wc156s9SrcT_lb : QuotientRankAtLeast step109wc156s9SrcT 14 := by
  have ht := quotientRankAtLeast_transpose step99_orbit55_lb14_unconditional
  have hle : step109wc156s9SrcT ≤ transposeW o55W := by
    unfold step109wc156s9SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4 | h5
    · subst h0
      show codeMat 272 ∈ Submodule.map transposeLinearMap o55W
      exact ⟨codeMat 272, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 272 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 128 ∈ Submodule.map transposeLinearMap o55W
      exact ⟨codeMat 32, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 32 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 66 ∈ Submodule.map transposeLinearMap o55W
      exact ⟨codeMat 12, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 12 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 34 ∈ Submodule.map transposeLinearMap o55W
      exact ⟨codeMat 136, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 136 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 8 ∈ Submodule.map transposeLinearMap o55W
      exact ⟨codeMat 2, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 2 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h5
      show codeMat 1 ∈ Submodule.map transposeLinearMap o55W
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc156s9_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc156s9_contain :
    (o156SourceU_wc ⟨9, by omega⟩) ≤ actionW (codeMat 84) (codeMat 140) step109wc156s9SrcT := by
  change spanCodes [256, 68, 32, 20, 10, 1] ≤ actionW (codeMat 84) (codeMat 140) step109wc156s9SrcT
  apply step109wc156_spanCodes_le_of_gens [256, 68, 32, 20, 10, 1]
    (actionW (codeMat 84) (codeMat 140) step109wc156s9SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 1 ∈ step109wc156s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step109wc156s9_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 66 ∈ step109wc156s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 66 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 66) = codeMat 68 := by
      unfold actionA
      rw [step109wc156s9_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 66 * (codeMat 98 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ step109wc156s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc156s9_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 96 ∈ step109wc156s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 96 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 96) = codeMat 20 := by
      unfold actionA
      rw [step109wc156s9_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 96 * (codeMat 98 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 272 ∈ step109wc156s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 272 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 272) = codeMat 10 := by
      unfold actionA
      rw [step109wc156s9_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 272 * (codeMat 98 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ step109wc156s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc156s9_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact

theorem step109wc156s9Dispatch :
    QuotientRankAtLeast (o156SourceU_wc ⟨9, by omega⟩) 14 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 140) step109wc156s9SrcT) 14 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 140) hP hQ step109wc156s9SrcT 14
      step109wc156s9SrcT_lb
  exact quotientRankAtLeast_mono step109wc156s9_contain hAct

private def step109wc156s10SrcT : Submodule F2 Mat3 := spanCodes [272, 128, 66, 34, 8, 1]

private theorem step109wc156s10SrcT_lb : QuotientRankAtLeast step109wc156s10SrcT 14 := by
  have ht := quotientRankAtLeast_transpose step99_orbit55_lb14_unconditional
  have hle : step109wc156s10SrcT ≤ transposeW o55W := by
    unfold step109wc156s10SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4 | h5
    · subst h0
      show codeMat 272 ∈ Submodule.map transposeLinearMap o55W
      exact ⟨codeMat 272, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 272 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 128 ∈ Submodule.map transposeLinearMap o55W
      exact ⟨codeMat 32, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 32 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 66 ∈ Submodule.map transposeLinearMap o55W
      exact ⟨codeMat 12, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 12 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 34 ∈ Submodule.map transposeLinearMap o55W
      exact ⟨codeMat 136, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 136 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 8 ∈ Submodule.map transposeLinearMap o55W
      exact ⟨codeMat 2, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 2 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h5
      show codeMat 1 ∈ Submodule.map transposeLinearMap o55W
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc156s10_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc156s10_contain :
    (o156SourceU_wc ⟨10, by omega⟩) ≤ actionW (codeMat 85) (codeMat 140) step109wc156s10SrcT := by
  change spanCodes [260, 68, 32, 20, 10, 1] ≤ actionW (codeMat 85) (codeMat 140) step109wc156s10SrcT
  apply step109wc156_spanCodes_le_of_gens [260, 68, 32, 20, 10, 1]
    (actionW (codeMat 85) (codeMat 140) step109wc156s10SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 1 ∈ step109wc156s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 1 (by decide)
    have hact : actionA (codeMat 85) (codeMat 140) (codeMat 1) = codeMat 260 := by
      unfold actionA
      rw [step109wc156s10_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 194 ∈ step109wc156s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 194 (by decide)
    have hact : actionA (codeMat 85) (codeMat 140) (codeMat 194) = codeMat 68 := by
      unfold actionA
      rw [step109wc156s10_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 194 * (codeMat 98 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ step109wc156s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 8 (by decide)
    have hact : actionA (codeMat 85) (codeMat 140) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc156s10_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 96 ∈ step109wc156s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 96 (by decide)
    have hact : actionA (codeMat 85) (codeMat 140) (codeMat 96) = codeMat 20 := by
      unfold actionA
      rw [step109wc156s10_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 96 * (codeMat 98 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 272 ∈ step109wc156s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 272 (by decide)
    have hact : actionA (codeMat 85) (codeMat 140) (codeMat 272) = codeMat 10 := by
      unfold actionA
      rw [step109wc156s10_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 272 * (codeMat 98 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ step109wc156s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 128 (by decide)
    have hact : actionA (codeMat 85) (codeMat 140) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc156s10_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 128 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact

theorem step109wc156s10Dispatch :
    QuotientRankAtLeast (o156SourceU_wc ⟨10, by omega⟩) 14 := by
  have hP : Invertible (codeMat 85 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 85) (codeMat 140) step109wc156s10SrcT) 14 :=
    @quotientRankAtLeast_action (codeMat 85) (codeMat 140) hP hQ step109wc156s10SrcT 14
      step109wc156s10SrcT_lb
  exact quotientRankAtLeast_mono step109wc156s10_contain hAct

private def step109wc156s11SrcT : Submodule F2 Mat3 := spanCodes [272, 128, 66, 34, 8, 1]

private theorem step109wc156s11SrcT_lb : QuotientRankAtLeast step109wc156s11SrcT 14 := by
  have ht := quotientRankAtLeast_transpose step99_orbit55_lb14_unconditional
  have hle : step109wc156s11SrcT ≤ transposeW o55W := by
    unfold step109wc156s11SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4 | h5
    · subst h0
      show codeMat 272 ∈ Submodule.map transposeLinearMap o55W
      exact ⟨codeMat 272, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 272 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 128 ∈ Submodule.map transposeLinearMap o55W
      exact ⟨codeMat 32, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 32 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 66 ∈ Submodule.map transposeLinearMap o55W
      exact ⟨codeMat 12, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 12 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 34 ∈ Submodule.map transposeLinearMap o55W
      exact ⟨codeMat 136, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 136 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 8 ∈ Submodule.map transposeLinearMap o55W
      exact ⟨codeMat 2, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 2 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h5
      show codeMat 1 ∈ Submodule.map transposeLinearMap o55W
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc156s11_QtInv :
    (codeMat 428 : Mat3).transpose⁻¹ = (codeMat 107 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 428 : Mat3).transpose * (codeMat 107 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc156s11_contain :
    (o156SourceU_wc ⟨11, by omega⟩) ≤ actionW (codeMat 94) (codeMat 428) step109wc156s11SrcT := by
  change spanCodes [386, 68, 32, 20, 10, 1] ≤ actionW (codeMat 94) (codeMat 428) step109wc156s11SrcT
  apply step109wc156_spanCodes_le_of_gens [386, 68, 32, 20, 10, 1]
    (actionW (codeMat 94) (codeMat 428) step109wc156s11SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 475 ∈ step109wc156s11SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 475 (by decide)
    have hact : actionA (codeMat 94) (codeMat 428) (codeMat 475) = codeMat 386 := by
      unfold actionA
      rw [step109wc156s11_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 475 * (codeMat 107 : Mat3).transpose = codeMat 386
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 338 ∈ step109wc156s11SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 338 (by decide)
    have hact : actionA (codeMat 94) (codeMat 428) (codeMat 338) = codeMat 68 := by
      unfold actionA
      rw [step109wc156s11_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 338 * (codeMat 107 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 504 ∈ step109wc156s11SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 504 (by decide)
    have hact : actionA (codeMat 94) (codeMat 428) (codeMat 504) = codeMat 32 := by
      unfold actionA
      rw [step109wc156s11_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 504 * (codeMat 107 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 224 ∈ step109wc156s11SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 224 (by decide)
    have hact : actionA (codeMat 94) (codeMat 428) (codeMat 224) = codeMat 20 := by
      unfold actionA
      rw [step109wc156s11_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 224 * (codeMat 107 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 400 ∈ step109wc156s11SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 400 (by decide)
    have hact : actionA (codeMat 94) (codeMat 428) (codeMat 400) = codeMat 10 := by
      unfold actionA
      rw [step109wc156s11_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 400 * (codeMat 107 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ step109wc156s11SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 128 (by decide)
    have hact : actionA (codeMat 94) (codeMat 428) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc156s11_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 128 * (codeMat 107 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact

theorem step109wc156s11Dispatch :
    QuotientRankAtLeast (o156SourceU_wc ⟨11, by omega⟩) 14 := by
  have hP : Invertible (codeMat 94 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 428 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 94) (codeMat 428) step109wc156s11SrcT) 14 :=
    @quotientRankAtLeast_action (codeMat 94) (codeMat 428) hP hQ step109wc156s11SrcT 14
      step109wc156s11SrcT_lb
  exact quotientRankAtLeast_mono step109wc156s11_contain hAct

private def step109wc156s12SrcT : Submodule F2 Mat3 := spanCodes [272, 128, 66, 34, 8, 1]

private theorem step109wc156s12SrcT_lb : QuotientRankAtLeast step109wc156s12SrcT 14 := by
  have ht := quotientRankAtLeast_transpose step99_orbit55_lb14_unconditional
  have hle : step109wc156s12SrcT ≤ transposeW o55W := by
    unfold step109wc156s12SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4 | h5
    · subst h0
      show codeMat 272 ∈ Submodule.map transposeLinearMap o55W
      exact ⟨codeMat 272, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 272 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 128 ∈ Submodule.map transposeLinearMap o55W
      exact ⟨codeMat 32, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 32 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 66 ∈ Submodule.map transposeLinearMap o55W
      exact ⟨codeMat 12, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 12 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 34 ∈ Submodule.map transposeLinearMap o55W
      exact ⟨codeMat 136, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 136 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 8 ∈ Submodule.map transposeLinearMap o55W
      exact ⟨codeMat 2, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 2 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h5
      show codeMat 1 ∈ Submodule.map transposeLinearMap o55W
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc156s12_QtInv :
    (codeMat 428 : Mat3).transpose⁻¹ = (codeMat 107 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 428 : Mat3).transpose * (codeMat 107 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc156s12_contain :
    (o156SourceU_wc ⟨12, by omega⟩) ≤ actionW (codeMat 95) (codeMat 428) step109wc156s12SrcT := by
  change spanCodes [388, 68, 32, 20, 10, 1] ≤ actionW (codeMat 95) (codeMat 428) step109wc156s12SrcT
  apply step109wc156_spanCodes_le_of_gens [388, 68, 32, 20, 10, 1]
    (actionW (codeMat 95) (codeMat 428) step109wc156s12SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 475 ∈ step109wc156s12SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 475 (by decide)
    have hact : actionA (codeMat 95) (codeMat 428) (codeMat 475) = codeMat 388 := by
      unfold actionA
      rw [step109wc156s12_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 475 * (codeMat 107 : Mat3).transpose = codeMat 388
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 466 ∈ step109wc156s12SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 466 (by decide)
    have hact : actionA (codeMat 95) (codeMat 428) (codeMat 466) = codeMat 68 := by
      unfold actionA
      rw [step109wc156s12_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 466 * (codeMat 107 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 504 ∈ step109wc156s12SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 504 (by decide)
    have hact : actionA (codeMat 95) (codeMat 428) (codeMat 504) = codeMat 32 := by
      unfold actionA
      rw [step109wc156s12_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 504 * (codeMat 107 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 224 ∈ step109wc156s12SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 224 (by decide)
    have hact : actionA (codeMat 95) (codeMat 428) (codeMat 224) = codeMat 20 := by
      unfold actionA
      rw [step109wc156s12_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 224 * (codeMat 107 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 400 ∈ step109wc156s12SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 400 (by decide)
    have hact : actionA (codeMat 95) (codeMat 428) (codeMat 400) = codeMat 10 := by
      unfold actionA
      rw [step109wc156s12_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 400 * (codeMat 107 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ step109wc156s12SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 128 (by decide)
    have hact : actionA (codeMat 95) (codeMat 428) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc156s12_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 128 * (codeMat 107 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact

theorem step109wc156s12Dispatch :
    QuotientRankAtLeast (o156SourceU_wc ⟨12, by omega⟩) 14 := by
  have hP : Invertible (codeMat 95 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 428 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 95) (codeMat 428) step109wc156s12SrcT) 14 :=
    @quotientRankAtLeast_action (codeMat 95) (codeMat 428) hP hQ step109wc156s12SrcT 14
      step109wc156s12SrcT_lb
  exact quotientRankAtLeast_mono step109wc156s12_contain hAct


private theorem step109wc156s13_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc156s13_contain :
    (o156SourceU_wc ⟨13, by omega⟩) ≤ actionW (codeMat 273) (codeMat 140) monoW_32 := by
  change spanCodes [64, 32, 16, 10, 4, 1] ≤ actionW (codeMat 273) (codeMat 140) monoW_32
  apply step109wc156_spanCodes_le_of_gens [64, 32, 16, 10, 4, 1]
    (actionW (codeMat 273) (codeMat 140) monoW_32)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 128 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 128) = codeMat 64 := by
      unfold actionA
      rw [step109wc156s13_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 128 * (codeMat 98 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 8 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc156s13_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 32 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 32) = codeMat 16 := by
      unfold actionA
      rw [step109wc156s13_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 32 * (codeMat 98 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 20 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 20 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 20) = codeMat 10 := by
      unfold actionA
      rw [step109wc156s13_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 20 * (codeMat 98 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 1) = codeMat 4 := by
      unfold actionA
      rw [step109wc156s13_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc156s13_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact

theorem step109wc156s13Dispatch :
    QuotientRankAtLeast (o156SourceU_wc ⟨13, by omega⟩) 12 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 140) monoW_32) 12 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 140) hP hQ monoW_32 12
      step99_mono_32_lb12
  exact quotientRankAtLeast_mono step109wc156s13_contain hAct


private theorem step109wc156s14_QtInv :
    (codeMat 410 : Mat3).transpose⁻¹ = (codeMat 331 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 410 : Mat3).transpose * (codeMat 331 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc156s14_contain :
    (o156SourceU_wc ⟨14, by omega⟩) ≤ actionW (codeMat 401) (codeMat 410) monoW_32 := by
  change spanCodes [66, 32, 18, 10, 6, 1] ≤ actionW (codeMat 401) (codeMat 410) monoW_32
  apply step109wc156_spanCodes_le_of_gens [66, 32, 18, 10, 6, 1]
    (actionW (codeMat 401) (codeMat 410) monoW_32)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 151 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 151 (by decide)
    have hact : actionA (codeMat 401) (codeMat 410) (codeMat 151) = codeMat 66 := by
      unfold actionA
      rw [step109wc156s14_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 151 * (codeMat 331 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 32 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 401) (codeMat 410) (codeMat 32) = codeMat 32 := by
      unfold actionA
      rw [step109wc156s14_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 32 * (codeMat 331 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 63 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 63 (by decide)
    have hact : actionA (codeMat 401) (codeMat 410) (codeMat 63) = codeMat 18 := by
      unfold actionA
      rw [step109wc156s14_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 63 * (codeMat 331 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 23 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 23 (by decide)
    have hact : actionA (codeMat 401) (codeMat 410) (codeMat 23) = codeMat 10 := by
      unfold actionA
      rw [step109wc156s14_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 23 * (codeMat 331 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 401) (codeMat 410) (codeMat 3) = codeMat 6 := by
      unfold actionA
      rw [step109wc156s14_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 3 * (codeMat 331 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 401) (codeMat 410) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc156s14_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 2 * (codeMat 331 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc156_codeMat_mem_actionW_of_witness hw hact

theorem step109wc156s14Dispatch :
    QuotientRankAtLeast (o156SourceU_wc ⟨14, by omega⟩) 12 := by
  have hP : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 410 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 401) (codeMat 410) monoW_32) 12 :=
    @quotientRankAtLeast_action (codeMat 401) (codeMat 410) hP hQ monoW_32 12
      step99_mono_32_lb12
  exact quotientRankAtLeast_mono step109wc156s14_contain hAct

theorem step109wc156_all_dispatch (i : Fin 15) :
    QuotientRankAtLeast (o156SourceU_wc i) (o156SourceLb_wc i) := by
  fin_cases i
  · exact step109wc156s0Dispatch
  · exact step109wc156s1Dispatch
  · exact step109wc156s2Dispatch
  · exact step109wc156s3Dispatch
  · exact step109wc156s4Dispatch
  · exact step109wc156s5Dispatch
  · exact step109wc156s6Dispatch
  · exact step109wc156s7Dispatch
  · exact step109wc156s8Dispatch
  · exact step109wc156s9Dispatch
  · exact step109wc156s10Dispatch
  · exact step109wc156s11Dispatch
  · exact step109wc156s12Dispatch
  · exact step109wc156s13Dispatch
  · exact step109wc156s14Dispatch

theorem step109_orbit156_lb16_wc : QuotientRankAtLeast o156W_wc 16 :=
  o156Lb16_wc step109wc156_all_dispatch

end QiushiMatmul
