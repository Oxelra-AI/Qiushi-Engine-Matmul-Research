import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit204Consumer
import QiushiWcOrbit64Dispatch
import QiushiWcOrbit47Dispatch
import QiushiWcOrbit83Dispatch
import QiushiOrbit10FP

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc204_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc204_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc204s0_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc204s0_contain :
    (o204SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 266) (codeMat 266) o64W_wc := by
  change spanCodes [258, 160, 68, 16, 10, 1] ≤ actionW (codeMat 266) (codeMat 266) o64W_wc
  apply step109wc204_spanCodes_le_of_gens [258, 160, 68, 16, 10, 1]
    (actionW (codeMat 266) (codeMat 266) o64W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 264 ∈ o64W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 68, 16, 10, 1] 264 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 264) = codeMat 258 := by
      unfold actionA
      rw [step109wc204s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 264 * (codeMat 266 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 68 ∈ o64W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 68, 16, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 68) = codeMat 160 := by
      unfold actionA
      rw [step109wc204s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 68 * (codeMat 266 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 160 ∈ o64W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 68, 16, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 160) = codeMat 68 := by
      unfold actionA
      rw [step109wc204s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 160 * (codeMat 266 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o64W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 68, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step109wc204s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 10 ∈ o64W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 68, 16, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step109wc204s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 10 * (codeMat 266 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ o64W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc204s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact

theorem step109wc204s0Dispatch :
    QuotientRankAtLeast (o204SourceU_wc ⟨0, by omega⟩) 15 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 266) o64W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 266) hP hQ o64W_wc 15
      step109_orbit64_lb15_wc
  exact quotientRankAtLeast_mono step109wc204s0_contain hAct


private theorem step109wc204s1_QtInv :
    (codeMat 188 : Mat3).transpose⁻¹ = (codeMat 103 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 188 : Mat3).transpose * (codeMat 103 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc204s1_contain :
    (o204SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 140) (codeMat 188) o64W_wc := by
  change spanCodes [260, 166, 68, 22, 10, 1] ≤ actionW (codeMat 140) (codeMat 188) o64W_wc
  apply step109wc204_spanCodes_le_of_gens [260, 166, 68, 22, 10, 1]
    (actionW (codeMat 140) (codeMat 188) o64W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 27 ∈ o64W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 68, 16, 10, 1] 27 (by decide)
    have hact : actionA (codeMat 140) (codeMat 188) (codeMat 27) = codeMat 260 := by
      unfold actionA
      rw [step109wc204s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 27 * (codeMat 103 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 238 ∈ o64W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 68, 16, 10, 1] 238 (by decide)
    have hact : actionA (codeMat 140) (codeMat 188) (codeMat 238) = codeMat 166 := by
      unfold actionA
      rw [step109wc204s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 238 * (codeMat 103 : Mat3).transpose = codeMat 166
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 26 ∈ o64W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 68, 16, 10, 1] 26 (by decide)
    have hact : actionA (codeMat 140) (codeMat 188) (codeMat 26) = codeMat 68 := by
      unfold actionA
      rw [step109wc204s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 26 * (codeMat 103 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 424 ∈ o64W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 68, 16, 10, 1] 424 (by decide)
    have hact : actionA (codeMat 140) (codeMat 188) (codeMat 424) = codeMat 22 := by
      unfold actionA
      rw [step109wc204s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 424 * (codeMat 103 : Mat3).transpose = codeMat 22
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 176 ∈ o64W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 68, 16, 10, 1] 176 (by decide)
    have hact : actionA (codeMat 140) (codeMat 188) (codeMat 176) = codeMat 10 := by
      unfold actionA
      rw [step109wc204s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 176 * (codeMat 103 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ o64W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 140) (codeMat 188) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc204s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 16 * (codeMat 103 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact

theorem step109wc204s1Dispatch :
    QuotientRankAtLeast (o204SourceU_wc ⟨1, by omega⟩) 15 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 188 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 188) o64W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 188) hP hQ o64W_wc 15
      step109_orbit64_lb15_wc
  exact quotientRankAtLeast_mono step109wc204s1_contain hAct


private theorem step109wc204s2_QtInv :
    (codeMat 305 : Mat3).transpose⁻¹ = (codeMat 305 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 305 : Mat3).transpose * (codeMat 305 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc204s2_contain :
    (o204SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 273) (codeMat 305) o47W_wc := by
  change spanCodes [272, 176, 68, 8, 2, 1] ≤ actionW (codeMat 273) (codeMat 305) o47W_wc
  apply step109wc204_spanCodes_le_of_gens [272, 176, 68, 8, 2, 1]
    (actionW (codeMat 273) (codeMat 305) o47W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 400 ∈ o47W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [304, 160, 68, 8, 2, 1] 400 (by decide)
    have hact : actionA (codeMat 273) (codeMat 305) (codeMat 400) = codeMat 272 := by
      unfold actionA
      rw [step109wc204s2_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 400 * (codeMat 305 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ o47W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [304, 160, 68, 8, 2, 1] 160 (by decide)
    have hact : actionA (codeMat 273) (codeMat 305) (codeMat 160) = codeMat 176 := by
      unfold actionA
      rw [step109wc204s2_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 160 * (codeMat 305 : Mat3).transpose = codeMat 176
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 70 ∈ o47W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [304, 160, 68, 8, 2, 1] 70 (by decide)
    have hact : actionA (codeMat 273) (codeMat 305) (codeMat 70) = codeMat 68 := by
      unfold actionA
      rw [step109wc204s2_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 70 * (codeMat 305 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ o47W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [304, 160, 68, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 305) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step109wc204s2_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 305 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o47W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [304, 160, 68, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 305) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc204s2_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 305 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o47W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [304, 160, 68, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 305) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc204s2_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 305 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact

theorem step109wc204s2Dispatch :
    QuotientRankAtLeast (o204SourceU_wc ⟨2, by omega⟩) 14 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 305) o47W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 305) hP hQ o47W_wc 14
      step109_orbit47_lb14_wc
  exact quotientRankAtLeast_mono step109wc204s2_contain hAct


private theorem step109wc204s3_QtInv :
    (codeMat 183 : Mat3).transpose⁻¹ = (codeMat 419 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 183 : Mat3).transpose * (codeMat 419 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc204s3_contain :
    (o204SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 161) (codeMat 183) o47W_wc := by
  change spanCodes [274, 176, 64, 10, 4, 1] ≤ actionW (codeMat 161) (codeMat 183) o47W_wc
  apply step109wc204_spanCodes_le_of_gens [274, 176, 64, 10, 4, 1]
    (actionW (codeMat 161) (codeMat 183) o47W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 479 ∈ o47W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [304, 160, 68, 8, 2, 1] 479 (by decide)
    have hact : actionA (codeMat 161) (codeMat 183) (codeMat 479) = codeMat 274 := by
      unfold actionA
      rw [step109wc204s3_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 479 * (codeMat 419 : Mat3).transpose = codeMat 274
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 312 ∈ o47W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [304, 160, 68, 8, 2, 1] 312 (by decide)
    have hact : actionA (codeMat 161) (codeMat 183) (codeMat 312) = codeMat 176 := by
      unfold actionA
      rw [step109wc204s3_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 312 * (codeMat 419 : Mat3).transpose = codeMat 176
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ o47W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [304, 160, 68, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 161) (codeMat 183) (codeMat 8) = codeMat 64 := by
      unfold actionA
      rw [step109wc204s3_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 8 * (codeMat 419 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 71 ∈ o47W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [304, 160, 68, 8, 2, 1] 71 (by decide)
    have hact : actionA (codeMat 161) (codeMat 183) (codeMat 71) = codeMat 10 := by
      unfold actionA
      rw [step109wc204s3_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 71 * (codeMat 419 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ o47W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [304, 160, 68, 8, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 161) (codeMat 183) (codeMat 3) = codeMat 4 := by
      unfold actionA
      rw [step109wc204s3_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 3 * (codeMat 419 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o47W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [304, 160, 68, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 183) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc204s3_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 419 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact

theorem step109wc204s3Dispatch :
    QuotientRankAtLeast (o204SourceU_wc ⟨3, by omega⟩) 14 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 183 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 183) o47W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 183) hP hQ o47W_wc 14
      step109_orbit47_lb14_wc
  exact quotientRankAtLeast_mono step109wc204s3_contain hAct


private theorem step109wc204s4_QtInv :
    (codeMat 421 : Mat3).transpose⁻¹ = (codeMat 179 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 421 : Mat3).transpose * (codeMat 179 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc204s4_contain :
    (o204SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 241) (codeMat 421) o83W_wc := by
  change spanCodes [274, 144, 68, 32, 10, 1] ≤ actionW (codeMat 241) (codeMat 421) o83W_wc
  apply step109wc204_spanCodes_le_of_gens [274, 144, 68, 32, 10, 1]
    (actionW (codeMat 241) (codeMat 421) o83W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 255 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 255 (by decide)
    have hact : actionA (codeMat 241) (codeMat 421) (codeMat 255) = codeMat 274 := by
      unfold actionA
      rw [step109wc204s4_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 255 * (codeMat 179 : Mat3).transpose = codeMat 274
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 32 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 241) (codeMat 421) (codeMat 32) = codeMat 144 := by
      unfold actionA
      rw [step109wc204s4_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 32 * (codeMat 179 : Mat3).transpose = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 78 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 78 (by decide)
    have hact : actionA (codeMat 241) (codeMat 421) (codeMat 78) = codeMat 68 := by
      unfold actionA
      rw [step109wc204s4_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 78 * (codeMat 179 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 455 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 455 (by decide)
    have hact : actionA (codeMat 241) (codeMat 421) (codeMat 455) = codeMat 32 := by
      unfold actionA
      rw [step109wc204s4_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 455 * (codeMat 179 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 69 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 69 (by decide)
    have hact : actionA (codeMat 241) (codeMat 421) (codeMat 69) = codeMat 10 := by
      unfold actionA
      rw [step109wc204s4_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 69 * (codeMat 179 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 241) (codeMat 421) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc204s4_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 1 * (codeMat 179 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact

theorem step109wc204s4Dispatch :
    QuotientRankAtLeast (o204SourceU_wc ⟨4, by omega⟩) 14 := by
  have hP : Invertible (codeMat 241 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 421 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 241) (codeMat 421) o83W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 241) (codeMat 421) hP hQ o83W_wc 14
      step109_orbit83_lb14_wc
  exact quotientRankAtLeast_mono step109wc204s4_contain hAct


private theorem step109wc204s5_QtInv :
    (codeMat 417 : Mat3).transpose⁻¹ = (codeMat 177 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 417 : Mat3).transpose * (codeMat 177 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc204s5_contain :
    (o204SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 249) (codeMat 417) o83W_wc := by
  change spanCodes [274, 146, 68, 34, 10, 1] ≤ actionW (codeMat 249) (codeMat 417) o83W_wc
  apply step109wc204_spanCodes_le_of_gens [274, 146, 68, 34, 10, 1]
    (actionW (codeMat 249) (codeMat 417) o83W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 176 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 176 (by decide)
    have hact : actionA (codeMat 249) (codeMat 417) (codeMat 176) = codeMat 274 := by
      unfold actionA
      rw [step109wc204s5_QtInv]
      show (codeMat 249 : Mat3).transpose * codeMat 176 * (codeMat 177 : Mat3).transpose = codeMat 274
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 32 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 249) (codeMat 417) (codeMat 32) = codeMat 146 := by
      unfold actionA
      rw [step109wc204s5_QtInv]
      show (codeMat 249 : Mat3).transpose * codeMat 32 * (codeMat 177 : Mat3).transpose = codeMat 146
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 78 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 78 (by decide)
    have hact : actionA (codeMat 249) (codeMat 417) (codeMat 78) = codeMat 68 := by
      unfold actionA
      rw [step109wc204s5_QtInv]
      show (codeMat 249 : Mat3).transpose * codeMat 78 * (codeMat 177 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 386 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 386 (by decide)
    have hact : actionA (codeMat 249) (codeMat 417) (codeMat 386) = codeMat 34 := by
      unfold actionA
      rw [step109wc204s5_QtInv]
      show (codeMat 249 : Mat3).transpose * codeMat 386 * (codeMat 177 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 69 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 69 (by decide)
    have hact : actionA (codeMat 249) (codeMat 417) (codeMat 69) = codeMat 10 := by
      unfold actionA
      rw [step109wc204s5_QtInv]
      show (codeMat 249 : Mat3).transpose * codeMat 69 * (codeMat 177 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 249) (codeMat 417) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc204s5_QtInv]
      show (codeMat 249 : Mat3).transpose * codeMat 1 * (codeMat 177 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact

theorem step109wc204s5Dispatch :
    QuotientRankAtLeast (o204SourceU_wc ⟨5, by omega⟩) 14 := by
  have hP : Invertible (codeMat 249 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 249) (codeMat 417) o83W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 249) (codeMat 417) hP hQ o83W_wc 14
      step109_orbit83_lb14_wc
  exact quotientRankAtLeast_mono step109wc204s5_contain hAct


private theorem step109wc204s6_QtInv :
    (codeMat 423 : Mat3).transpose⁻¹ = (codeMat 181 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 423 : Mat3).transpose * (codeMat 181 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc204s6_contain :
    (o204SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 185) (codeMat 423) o83W_wc := by
  change spanCodes [274, 148, 68, 36, 10, 1] ≤ actionW (codeMat 185) (codeMat 423) o83W_wc
  apply step109wc204_spanCodes_le_of_gens [274, 148, 68, 36, 10, 1]
    (actionW (codeMat 185) (codeMat 423) o83W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 186 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 186 (by decide)
    have hact : actionA (codeMat 185) (codeMat 423) (codeMat 186) = codeMat 274 := by
      unfold actionA
      rw [step109wc204s6_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 186 * (codeMat 181 : Mat3).transpose = codeMat 274
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 42 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 42 (by decide)
    have hact : actionA (codeMat 185) (codeMat 423) (codeMat 42) = codeMat 148 := by
      unfold actionA
      rw [step109wc204s6_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 42 * (codeMat 181 : Mat3).transpose = codeMat 148
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 78 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 78 (by decide)
    have hact : actionA (codeMat 185) (codeMat 423) (codeMat 78) = codeMat 68 := by
      unfold actionA
      rw [step109wc204s6_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 78 * (codeMat 181 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 455 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 455 (by decide)
    have hact : actionA (codeMat 185) (codeMat 423) (codeMat 455) = codeMat 36 := by
      unfold actionA
      rw [step109wc204s6_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 455 * (codeMat 181 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 69 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 69 (by decide)
    have hact : actionA (codeMat 185) (codeMat 423) (codeMat 69) = codeMat 10 := by
      unfold actionA
      rw [step109wc204s6_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 69 * (codeMat 181 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 185) (codeMat 423) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc204s6_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 1 * (codeMat 181 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact

theorem step109wc204s6Dispatch :
    QuotientRankAtLeast (o204SourceU_wc ⟨6, by omega⟩) 14 := by
  have hP : Invertible (codeMat 185 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 423 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 185) (codeMat 423) o83W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 185) (codeMat 423) hP hQ o83W_wc 14
      step109_orbit83_lb14_wc
  exact quotientRankAtLeast_mono step109wc204s6_contain hAct


private theorem step109wc204s7_QtInv :
    (codeMat 419 : Mat3).transpose⁻¹ = (codeMat 183 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 419 : Mat3).transpose * (codeMat 183 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc204s7_contain :
    (o204SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 177) (codeMat 419) o83W_wc := by
  change spanCodes [274, 150, 68, 38, 10, 1] ≤ actionW (codeMat 177) (codeMat 419) o83W_wc
  apply step109wc204_spanCodes_le_of_gens [274, 150, 68, 38, 10, 1]
    (actionW (codeMat 177) (codeMat 419) o83W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 245 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 245 (by decide)
    have hact : actionA (codeMat 177) (codeMat 419) (codeMat 245) = codeMat 274 := by
      unfold actionA
      rw [step109wc204s7_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 245 * (codeMat 183 : Mat3).transpose = codeMat 274
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 43 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 43 (by decide)
    have hact : actionA (codeMat 177) (codeMat 419) (codeMat 43) = codeMat 150 := by
      unfold actionA
      rw [step109wc204s7_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 43 * (codeMat 183 : Mat3).transpose = codeMat 150
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 78 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 78 (by decide)
    have hact : actionA (codeMat 177) (codeMat 419) (codeMat 78) = codeMat 68 := by
      unfold actionA
      rw [step109wc204s7_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 78 * (codeMat 183 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 387 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 387 (by decide)
    have hact : actionA (codeMat 177) (codeMat 419) (codeMat 387) = codeMat 38 := by
      unfold actionA
      rw [step109wc204s7_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 387 * (codeMat 183 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 69 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 69 (by decide)
    have hact : actionA (codeMat 177) (codeMat 419) (codeMat 69) = codeMat 10 := by
      unfold actionA
      rw [step109wc204s7_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 69 * (codeMat 183 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 419) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc204s7_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * (codeMat 183 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact

theorem step109wc204s7Dispatch :
    QuotientRankAtLeast (o204SourceU_wc ⟨7, by omega⟩) 14 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 419 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 419) o83W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 419) hP hQ o83W_wc 14
      step109_orbit83_lb14_wc
  exact quotientRankAtLeast_mono step109wc204s7_contain hAct


private theorem step109wc204s8_QtInv :
    (codeMat 165 : Mat3).transpose⁻¹ = (codeMat 163 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 165 : Mat3).transpose * (codeMat 163 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc204s8_contain :
    (o204SourceU_wc ⟨8, by omega⟩) ≤ actionW (codeMat 225) (codeMat 165) o83W_wc := by
  change spanCodes [274, 128, 68, 48, 10, 1] ≤ actionW (codeMat 225) (codeMat 165) o83W_wc
  apply step109wc204_spanCodes_le_of_gens [274, 128, 68, 48, 10, 1]
    (actionW (codeMat 225) (codeMat 165) o83W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 280 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 280 (by decide)
    have hact : actionA (codeMat 225) (codeMat 165) (codeMat 280) = codeMat 274 := by
      unfold actionA
      rw [step109wc204s8_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 280 * (codeMat 163 : Mat3).transpose = codeMat 274
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 32 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 225) (codeMat 165) (codeMat 32) = codeMat 128 := by
      unfold actionA
      rw [step109wc204s8_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 32 * (codeMat 163 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 11 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 225) (codeMat 165) (codeMat 11) = codeMat 68 := by
      unfold actionA
      rw [step109wc204s8_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 11 * (codeMat 163 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 455 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 455 (by decide)
    have hact : actionA (codeMat 225) (codeMat 165) (codeMat 455) = codeMat 48 := by
      unfold actionA
      rw [step109wc204s8_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 455 * (codeMat 163 : Mat3).transpose = codeMat 48
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 69 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 69 (by decide)
    have hact : actionA (codeMat 225) (codeMat 165) (codeMat 69) = codeMat 10 := by
      unfold actionA
      rw [step109wc204s8_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 69 * (codeMat 163 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 225) (codeMat 165) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc204s8_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 1 * (codeMat 163 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact

theorem step109wc204s8Dispatch :
    QuotientRankAtLeast (o204SourceU_wc ⟨8, by omega⟩) 14 := by
  have hP : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 165 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 225) (codeMat 165) o83W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 225) (codeMat 165) hP hQ o83W_wc 14
      step109_orbit83_lb14_wc
  exact quotientRankAtLeast_mono step109wc204s8_contain hAct


private theorem step109wc204s9_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc204s9_contain :
    (o204SourceU_wc ⟨9, by omega⟩) ≤ actionW (codeMat 233) (codeMat 161) o83W_wc := by
  change spanCodes [274, 130, 68, 50, 10, 1] ≤ actionW (codeMat 233) (codeMat 161) o83W_wc
  apply step109wc204_spanCodes_le_of_gens [274, 130, 68, 50, 10, 1]
    (actionW (codeMat 233) (codeMat 161) o83W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 274 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 274 (by decide)
    have hact : actionA (codeMat 233) (codeMat 161) (codeMat 274) = codeMat 274 := by
      unfold actionA
      rw [step109wc204s9_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 274 * (codeMat 161 : Mat3).transpose = codeMat 274
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 32 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 233) (codeMat 161) (codeMat 32) = codeMat 130 := by
      unfold actionA
      rw [step109wc204s9_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 32 * (codeMat 161 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 11 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 233) (codeMat 161) (codeMat 11) = codeMat 68 := by
      unfold actionA
      rw [step109wc204s9_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 11 * (codeMat 161 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 386 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 386 (by decide)
    have hact : actionA (codeMat 233) (codeMat 161) (codeMat 386) = codeMat 50 := by
      unfold actionA
      rw [step109wc204s9_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 386 * (codeMat 161 : Mat3).transpose = codeMat 50
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 69 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 69 (by decide)
    have hact : actionA (codeMat 233) (codeMat 161) (codeMat 69) = codeMat 10 := by
      unfold actionA
      rw [step109wc204s9_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 69 * (codeMat 161 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 233) (codeMat 161) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc204s9_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact

theorem step109wc204s9Dispatch :
    QuotientRankAtLeast (o204SourceU_wc ⟨9, by omega⟩) 14 := by
  have hP : Invertible (codeMat 233 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 233) (codeMat 161) o83W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 233) (codeMat 161) hP hQ o83W_wc 14
      step109_orbit83_lb14_wc
  exact quotientRankAtLeast_mono step109wc204s9_contain hAct


private theorem step109wc204s10_QtInv :
    (codeMat 167 : Mat3).transpose⁻¹ = (codeMat 167 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 167 : Mat3).transpose * (codeMat 167 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc204s10_contain :
    (o204SourceU_wc ⟨10, by omega⟩) ≤ actionW (codeMat 161) (codeMat 167) o83W_wc := by
  change spanCodes [274, 132, 68, 52, 10, 1] ≤ actionW (codeMat 161) (codeMat 167) o83W_wc
  apply step109wc204_spanCodes_le_of_gens [274, 132, 68, 52, 10, 1]
    (actionW (codeMat 161) (codeMat 167) o83W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 349 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 349 (by decide)
    have hact : actionA (codeMat 161) (codeMat 167) (codeMat 349) = codeMat 274 := by
      unfold actionA
      rw [step109wc204s10_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 349 * (codeMat 167 : Mat3).transpose = codeMat 274
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 43 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 43 (by decide)
    have hact : actionA (codeMat 161) (codeMat 167) (codeMat 43) = codeMat 132 := by
      unfold actionA
      rw [step109wc204s10_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 43 * (codeMat 167 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 11 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 161) (codeMat 167) (codeMat 11) = codeMat 68 := by
      unfold actionA
      rw [step109wc204s10_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 11 * (codeMat 167 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 387 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 387 (by decide)
    have hact : actionA (codeMat 161) (codeMat 167) (codeMat 387) = codeMat 52 := by
      unfold actionA
      rw [step109wc204s10_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 387 * (codeMat 167 : Mat3).transpose = codeMat 52
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 69 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 69 (by decide)
    have hact : actionA (codeMat 161) (codeMat 167) (codeMat 69) = codeMat 10 := by
      unfold actionA
      rw [step109wc204s10_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 69 * (codeMat 167 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 167) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc204s10_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 167 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact

theorem step109wc204s10Dispatch :
    QuotientRankAtLeast (o204SourceU_wc ⟨10, by omega⟩) 14 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 167 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 167) o83W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 167) hP hQ o83W_wc 14
      step109_orbit83_lb14_wc
  exact quotientRankAtLeast_mono step109wc204s10_contain hAct


private theorem step109wc204s11_QtInv :
    (codeMat 163 : Mat3).transpose⁻¹ = (codeMat 165 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 163 : Mat3).transpose * (codeMat 165 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc204s11_contain :
    (o204SourceU_wc ⟨11, by omega⟩) ≤ actionW (codeMat 169) (codeMat 163) o83W_wc := by
  change spanCodes [274, 134, 68, 54, 10, 1] ≤ actionW (codeMat 169) (codeMat 163) o83W_wc
  apply step109wc204_spanCodes_le_of_gens [274, 134, 68, 54, 10, 1]
    (actionW (codeMat 169) (codeMat 163) o83W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 343 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 343 (by decide)
    have hact : actionA (codeMat 169) (codeMat 163) (codeMat 343) = codeMat 274 := by
      unfold actionA
      rw [step109wc204s11_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 343 * (codeMat 165 : Mat3).transpose = codeMat 274
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 42 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 42 (by decide)
    have hact : actionA (codeMat 169) (codeMat 163) (codeMat 42) = codeMat 134 := by
      unfold actionA
      rw [step109wc204s11_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 42 * (codeMat 165 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 11 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 169) (codeMat 163) (codeMat 11) = codeMat 68 := by
      unfold actionA
      rw [step109wc204s11_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 11 * (codeMat 165 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 455 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 455 (by decide)
    have hact : actionA (codeMat 169) (codeMat 163) (codeMat 455) = codeMat 54 := by
      unfold actionA
      rw [step109wc204s11_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 455 * (codeMat 165 : Mat3).transpose = codeMat 54
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 69 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 69 (by decide)
    have hact : actionA (codeMat 169) (codeMat 163) (codeMat 69) = codeMat 10 := by
      unfold actionA
      rw [step109wc204s11_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 69 * (codeMat 165 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 163) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc204s11_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * (codeMat 165 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact

theorem step109wc204s11Dispatch :
    QuotientRankAtLeast (o204SourceU_wc ⟨11, by omega⟩) 14 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 163 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 163) o83W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 163) hP hQ o83W_wc 14
      step109_orbit83_lb14_wc
  exact quotientRankAtLeast_mono step109wc204s11_contain hAct


private theorem step109wc204s12_QtInv :
    (codeMat 412 : Mat3).transpose⁻¹ = (codeMat 111 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 412 : Mat3).transpose * (codeMat 111 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc204s12_contain :
    (o204SourceU_wc ⟨12, by omega⟩) ≤ actionW (codeMat 142) (codeMat 412) orbit10W := by
  change spanCodes [256, 162, 66, 18, 10, 6, 1] ≤ actionW (codeMat 142) (codeMat 412) orbit10W
  apply step109wc204_spanCodes_le_of_gens [256, 162, 66, 18, 10, 6, 1]
    (actionW (codeMat 142) (codeMat 412) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 325 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 325 (by decide)
    have hact : actionA (codeMat 142) (codeMat 412) (codeMat 325) = codeMat 256 := by
      unfold actionA
      rw [step109wc204s12_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 325 * (codeMat 111 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 246 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 246 (by decide)
    have hact : actionA (codeMat 142) (codeMat 412) (codeMat 246) = codeMat 162 := by
      unfold actionA
      rw [step109wc204s12_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 246 * (codeMat 111 : Mat3).transpose = codeMat 162
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 178 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 178 (by decide)
    have hact : actionA (codeMat 142) (codeMat 412) (codeMat 178) = codeMat 66 := by
      unfold actionA
      rw [step109wc204s12_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 178 * (codeMat 111 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 432 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 432 (by decide)
    have hact : actionA (codeMat 142) (codeMat 412) (codeMat 432) = codeMat 18 := by
      unfold actionA
      rw [step109wc204s12_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 432 * (codeMat 111 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 176 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 176 (by decide)
    have hact : actionA (codeMat 142) (codeMat 412) (codeMat 176) = codeMat 10 := by
      unfold actionA
      rw [step109wc204s12_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 176 * (codeMat 111 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 24 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide)
    have hact : actionA (codeMat 142) (codeMat 412) (codeMat 24) = codeMat 6 := by
      unfold actionA
      rw [step109wc204s12_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 24 * (codeMat 111 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 142) (codeMat 412) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc204s12_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 16 * (codeMat 111 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc204_codeMat_mem_actionW_of_witness hw hact

theorem step109wc204s12Dispatch :
    QuotientRankAtLeast (o204SourceU_wc ⟨12, by omega⟩) 12 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 412 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 412) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 412) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc204s12_contain hAct

theorem step109wc204_all_dispatch (i : Fin 13) :
    QuotientRankAtLeast (o204SourceU_wc i) (o204SourceLb_wc i) := by
  fin_cases i
  · exact step109wc204s0Dispatch
  · exact step109wc204s1Dispatch
  · exact step109wc204s2Dispatch
  · exact step109wc204s3Dispatch
  · exact step109wc204s4Dispatch
  · exact step109wc204s5Dispatch
  · exact step109wc204s6Dispatch
  · exact step109wc204s7Dispatch
  · exact step109wc204s8Dispatch
  · exact step109wc204s9Dispatch
  · exact step109wc204s10Dispatch
  · exact step109wc204s11Dispatch
  · exact step109wc204s12Dispatch

theorem step109_orbit204_lb16_wc : QuotientRankAtLeast o204W_wc 16 :=
  o204Lb16_wc step109wc204_all_dispatch

end QiushiMatmul
