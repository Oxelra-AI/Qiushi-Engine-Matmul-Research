import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiWcOrbit334Consumer
import QiushiMonoOrbit108From29
import QiushiWcOrbit141Dispatch
import QiushiMonoOrbit148From29
import QiushiStep99Orbit231Dispatch
import QiushiMonoOrbit232From67
import QiushiWcOrbit233Dispatch
import QiushiMonoOrbit209From65
import QiushiStep128Mono215From78

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc334_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc334_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc334s0_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc334s0_contain :
    (o334SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 273) (codeMat 266) o108W_mono := by
  change spanCodes [140, 96, 16, 2, 1] ≤ actionW (codeMat 273) (codeMat 266) o108W_mono
  apply step109wc334_spanCodes_le_of_gens [140, 96, 16, 2, 1]
    (actionW (codeMat 273) (codeMat 266) o108W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 84 ∈ o108W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [160, 84, 8, 2, 1] 84 (by decide)
    have hact : actionA (codeMat 273) (codeMat 266) (codeMat 84) = codeMat 140 := by
      unfold actionA
      rw [step109wc334s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 84 * (codeMat 266 : Mat3).transpose = codeMat 140
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ o108W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [160, 84, 8, 2, 1] 160 (by decide)
    have hact : actionA (codeMat 273) (codeMat 266) (codeMat 160) = codeMat 96 := by
      unfold actionA
      rw [step109wc334s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 160 * (codeMat 266 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ o108W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [160, 84, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 266) (codeMat 8) = codeMat 16 := by
      unfold actionA
      rw [step109wc334s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 266 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o108W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [160, 84, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 266) (codeMat 1) = codeMat 2 := by
      unfold actionA
      rw [step109wc334s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o108W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [160, 84, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 266) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc334s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact

theorem step109wc334s0Dispatch :
    QuotientRankAtLeast (o334SourceU_wc ⟨0, by omega⟩) 15 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 266) o108W_mono) 15 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 266) hP hQ o108W_mono 15
      orbit108_lb15_mono
  exact quotientRankAtLeast_mono step109wc334s0_contain hAct


private theorem step109wc334s1_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc334s1_contain :
    (o334SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 273) (codeMat 161) o141W_wc := by
  change spanCodes [136, 98, 16, 4, 1] ≤ actionW (codeMat 273) (codeMat 161) o141W_wc
  apply step109wc334_spanCodes_le_of_gens [136, 98, 16, 4, 1]
    (actionW (codeMat 273) (codeMat 161) o141W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 264 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 264 (by decide)
    have hact : actionA (codeMat 273) (codeMat 161) (codeMat 264) = codeMat 136 := by
      unfold actionA
      rw [step109wc334s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 264 * (codeMat 161 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 84 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 84 (by decide)
    have hact : actionA (codeMat 273) (codeMat 161) (codeMat 84) = codeMat 98 := by
      unfold actionA
      rw [step109wc334s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 84 * (codeMat 161 : Mat3).transpose = codeMat 98
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 32 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 273) (codeMat 161) (codeMat 32) = codeMat 16 := by
      unfold actionA
      rw [step109wc334s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 32 * (codeMat 161 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 161) (codeMat 2) = codeMat 4 := by
      unfold actionA
      rw [step109wc334s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 161 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 161) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc334s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact

theorem step109wc334s1Dispatch :
    QuotientRankAtLeast (o334SourceU_wc ⟨1, by omega⟩) 15 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 161) o141W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 161) hP hQ o141W_wc 15
      step109_orbit141_lb15_wc
  exact quotientRankAtLeast_mono step109wc334s1_contain hAct


private theorem step109wc334s2_QtInv :
    (codeMat 417 : Mat3).transpose⁻¹ = (codeMat 177 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 417 : Mat3).transpose * (codeMat 177 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc334s2_contain :
    (o334SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 337) (codeMat 417) o141W_wc := by
  change spanCodes [138, 98, 16, 6, 1] ≤ actionW (codeMat 337) (codeMat 417) o141W_wc
  apply step109wc334_spanCodes_le_of_gens [138, 98, 16, 6, 1]
    (actionW (codeMat 337) (codeMat 417) o141W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 264 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 264 (by decide)
    have hact : actionA (codeMat 337) (codeMat 417) (codeMat 264) = codeMat 138 := by
      unfold actionA
      rw [step109wc334s2_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 264 * (codeMat 177 : Mat3).transpose = codeMat 138
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 117 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 117 (by decide)
    have hact : actionA (codeMat 337) (codeMat 417) (codeMat 117) = codeMat 98 := by
      unfold actionA
      rw [step109wc334s2_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 117 * (codeMat 177 : Mat3).transpose = codeMat 98
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 32 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 337) (codeMat 417) (codeMat 32) = codeMat 16 := by
      unfold actionA
      rw [step109wc334s2_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 32 * (codeMat 177 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 337) (codeMat 417) (codeMat 2) = codeMat 6 := by
      unfold actionA
      rw [step109wc334s2_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 2 * (codeMat 177 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 337) (codeMat 417) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc334s2_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 1 * (codeMat 177 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact

theorem step109wc334s2Dispatch :
    QuotientRankAtLeast (o334SourceU_wc ⟨2, by omega⟩) 15 := by
  have hP : Invertible (codeMat 337 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 337) (codeMat 417) o141W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 337) (codeMat 417) hP hQ o141W_wc 15
      step109_orbit141_lb15_wc
  exact quotientRankAtLeast_mono step109wc334s2_contain hAct


private theorem step109wc334s3_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc334s3_contain :
    (o334SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 266) (codeMat 273) o108W_mono := by
  change spanCodes [132, 98, 16, 8, 1] ≤ actionW (codeMat 266) (codeMat 273) o108W_mono
  apply step109wc334_spanCodes_le_of_gens [132, 98, 16, 8, 1]
    (actionW (codeMat 266) (codeMat 273) o108W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 160 ∈ o108W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [160, 84, 8, 2, 1] 160 (by decide)
    have hact : actionA (codeMat 266) (codeMat 273) (codeMat 160) = codeMat 132 := by
      unfold actionA
      rw [step109wc334s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 160 * (codeMat 273 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 84 ∈ o108W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [160, 84, 8, 2, 1] 84 (by decide)
    have hact : actionA (codeMat 266) (codeMat 273) (codeMat 84) = codeMat 98 := by
      unfold actionA
      rw [step109wc334s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 84 * (codeMat 273 : Mat3).transpose = codeMat 98
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ o108W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [160, 84, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 273) (codeMat 2) = codeMat 16 := by
      unfold actionA
      rw [step109wc334s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o108W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [160, 84, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 273) (codeMat 1) = codeMat 8 := by
      unfold actionA
      rw [step109wc334s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ o108W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [160, 84, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 273) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc334s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact

theorem step109wc334s3Dispatch :
    QuotientRankAtLeast (o334SourceU_wc ⟨3, by omega⟩) 15 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 273) o108W_mono) 15 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 273) hP hQ o108W_mono 15
      orbit108_lb15_mono
  exact quotientRankAtLeast_mono step109wc334s3_contain hAct


private theorem step109wc334s4_QtInv :
    (codeMat 286 : Mat3).transpose⁻¹ = (codeMat 303 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 286 : Mat3).transpose * (codeMat 303 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc334s4_contain :
    (o334SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 267) (codeMat 286) o148W_mono := by
  change spanCodes [134, 98, 16, 10, 1] ≤ actionW (codeMat 267) (codeMat 286) o148W_mono
  apply step109wc334_spanCodes_le_of_gens [134, 98, 16, 10, 1]
    (actionW (codeMat 267) (codeMat 286) o148W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 240 ∈ o148W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [164, 68, 16, 10, 1] 240 (by decide)
    have hact : actionA (codeMat 267) (codeMat 286) (codeMat 240) = codeMat 134 := by
      unfold actionA
      rw [step109wc334s4_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 240 * (codeMat 303 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 181 ∈ o148W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [164, 68, 16, 10, 1] 181 (by decide)
    have hact : actionA (codeMat 267) (codeMat 286) (codeMat 181) = codeMat 98 := by
      unfold actionA
      rw [step109wc334s4_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 181 * (codeMat 303 : Mat3).transpose = codeMat 98
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 27 ∈ o148W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [164, 68, 16, 10, 1] 27 (by decide)
    have hact : actionA (codeMat 267) (codeMat 286) (codeMat 27) = codeMat 16 := by
      unfold actionA
      rw [step109wc334s4_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 27 * (codeMat 303 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 10 ∈ o148W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [164, 68, 16, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 267) (codeMat 286) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step109wc334s4_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 10 * (codeMat 303 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 16 ∈ o148W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [164, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 267) (codeMat 286) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc334s4_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 16 * (codeMat 303 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact

theorem step109wc334s4Dispatch :
    QuotientRankAtLeast (o334SourceU_wc ⟨4, by omega⟩) 15 := by
  have hP : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 286 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 267) (codeMat 286) o148W_mono) 15 :=
    @quotientRankAtLeast_action (codeMat 267) (codeMat 286) hP hQ o148W_mono 15
      orbit148_lb15_mono
  exact quotientRankAtLeast_mono step109wc334s4_contain hAct

private def step109wc334s5SrcT : Submodule F2 Mat3 := spanCodes [258, 128, 84, 8, 1]

private theorem step109wc334s5SrcT_lb : QuotientRankAtLeast step109wc334s5SrcT 15 := by
  have ht := quotientRankAtLeast_transpose step109_orbit141_lb15_wc
  have hle : step109wc334s5SrcT ≤ transposeW o141W_wc := by
    unfold step109wc334s5SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4
    · subst h0
      show codeMat 258 ∈ Submodule.map transposeLinearMap o141W_wc
      exact ⟨codeMat 264, spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 264 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 128 ∈ Submodule.map transposeLinearMap o141W_wc
      exact ⟨codeMat 32, spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 32 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 84 ∈ Submodule.map transposeLinearMap o141W_wc
      exact ⟨codeMat 84, spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 84 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 8 ∈ Submodule.map transposeLinearMap o141W_wc
      exact ⟨codeMat 2, spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 2 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 1 ∈ Submodule.map transposeLinearMap o141W_wc
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc334s5_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc334s5_contain :
    (o334SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 98) (codeMat 266) step109wc334s5SrcT := by
  change spanCodes [128, 98, 16, 12, 1] ≤ actionW (codeMat 98) (codeMat 266) step109wc334s5SrcT
  apply step109wc334_spanCodes_le_of_gens [128, 98, 16, 12, 1]
    (actionW (codeMat 98) (codeMat 266) step109wc334s5SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 8 ∈ step109wc334s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 8, 1] 8 (by decide)
    have hact : actionA (codeMat 98) (codeMat 266) (codeMat 8) = codeMat 128 := by
      unfold actionA
      rw [step109wc334s5_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 8 * (codeMat 266 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 84 ∈ step109wc334s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 8, 1] 84 (by decide)
    have hact : actionA (codeMat 98) (codeMat 266) (codeMat 84) = codeMat 98 := by
      unfold actionA
      rw [step109wc334s5_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 84 * (codeMat 266 : Mat3).transpose = codeMat 98
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ step109wc334s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 8, 1] 1 (by decide)
    have hact : actionA (codeMat 98) (codeMat 266) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step109wc334s5_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 258 ∈ step109wc334s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 8, 1] 258 (by decide)
    have hact : actionA (codeMat 98) (codeMat 266) (codeMat 258) = codeMat 12 := by
      unfold actionA
      rw [step109wc334s5_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 258 * (codeMat 266 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 128 ∈ step109wc334s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 8, 1] 128 (by decide)
    have hact : actionA (codeMat 98) (codeMat 266) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc334s5_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 128 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact

theorem step109wc334s5Dispatch :
    QuotientRankAtLeast (o334SourceU_wc ⟨5, by omega⟩) 15 := by
  have hP : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 98) (codeMat 266) step109wc334s5SrcT) 15 :=
    @quotientRankAtLeast_action (codeMat 98) (codeMat 266) hP hQ step109wc334s5SrcT 15
      step109wc334s5SrcT_lb
  exact quotientRankAtLeast_mono step109wc334s5_contain hAct

private def step109wc334s6SrcT : Submodule F2 Mat3 := spanCodes [258, 128, 84, 8, 1]

private theorem step109wc334s6SrcT_lb : QuotientRankAtLeast step109wc334s6SrcT 15 := by
  have ht := quotientRankAtLeast_transpose step109_orbit141_lb15_wc
  have hle : step109wc334s6SrcT ≤ transposeW o141W_wc := by
    unfold step109wc334s6SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4
    · subst h0
      show codeMat 258 ∈ Submodule.map transposeLinearMap o141W_wc
      exact ⟨codeMat 264, spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 264 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 128 ∈ Submodule.map transposeLinearMap o141W_wc
      exact ⟨codeMat 32, spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 32 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 84 ∈ Submodule.map transposeLinearMap o141W_wc
      exact ⟨codeMat 84, spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 84 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 8 ∈ Submodule.map transposeLinearMap o141W_wc
      exact ⟨codeMat 2, spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 2 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 1 ∈ Submodule.map transposeLinearMap o141W_wc
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc334s6_QtInv :
    (codeMat 270 : Mat3).transpose⁻¹ = (codeMat 298 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 270 : Mat3).transpose * (codeMat 298 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc334s6_contain :
    (o334SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 106) (codeMat 270) step109wc334s6SrcT := by
  change spanCodes [130, 98, 16, 14, 1] ≤ actionW (codeMat 106) (codeMat 270) step109wc334s6SrcT
  apply step109wc334_spanCodes_le_of_gens [130, 98, 16, 14, 1]
    (actionW (codeMat 106) (codeMat 270) step109wc334s6SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 8 ∈ step109wc334s6SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 8, 1] 8 (by decide)
    have hact : actionA (codeMat 106) (codeMat 270) (codeMat 8) = codeMat 130 := by
      unfold actionA
      rw [step109wc334s6_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 8 * (codeMat 298 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 213 ∈ step109wc334s6SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 8, 1] 213 (by decide)
    have hact : actionA (codeMat 106) (codeMat 270) (codeMat 213) = codeMat 98 := by
      unfold actionA
      rw [step109wc334s6_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 213 * (codeMat 298 : Mat3).transpose = codeMat 98
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ step109wc334s6SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 8, 1] 1 (by decide)
    have hact : actionA (codeMat 106) (codeMat 270) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step109wc334s6_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 1 * (codeMat 298 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 258 ∈ step109wc334s6SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 8, 1] 258 (by decide)
    have hact : actionA (codeMat 106) (codeMat 270) (codeMat 258) = codeMat 14 := by
      unfold actionA
      rw [step109wc334s6_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 258 * (codeMat 298 : Mat3).transpose = codeMat 14
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 128 ∈ step109wc334s6SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 8, 1] 128 (by decide)
    have hact : actionA (codeMat 106) (codeMat 270) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc334s6_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 128 * (codeMat 298 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact

theorem step109wc334s6Dispatch :
    QuotientRankAtLeast (o334SourceU_wc ⟨6, by omega⟩) 15 := by
  have hP : Invertible (codeMat 106 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 270 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 106) (codeMat 270) step109wc334s6SrcT) 15 :=
    @quotientRankAtLeast_action (codeMat 106) (codeMat 270) hP hQ step109wc334s6SrcT 15
      step109wc334s6SrcT_lb
  exact quotientRankAtLeast_mono step109wc334s6_contain hAct


private theorem step109wc334s7_QtInv :
    (codeMat 98 : Mat3).transpose⁻¹ = (codeMat 140 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 98 : Mat3).transpose * (codeMat 140 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc334s7_contain :
    (o334SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 266) (codeMat 98) o141W_wc := by
  change spanCodes [140, 66, 32, 16, 1] ≤ actionW (codeMat 266) (codeMat 98) o141W_wc
  apply step109wc334_spanCodes_le_of_gens [140, 66, 32, 16, 1]
    (actionW (codeMat 266) (codeMat 98) o141W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 84 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 84 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 84) = codeMat 140 := by
      unfold actionA
      rw [step109wc334s7_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 84 * (codeMat 140 : Mat3).transpose = codeMat 140
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 264 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 264 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 264) = codeMat 66 := by
      unfold actionA
      rw [step109wc334s7_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 264 * (codeMat 140 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 2) = codeMat 32 := by
      unfold actionA
      rw [step109wc334s7_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 140 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step109wc334s7_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 140 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 32 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step109wc334s7_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 140 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact

theorem step109wc334s7Dispatch :
    QuotientRankAtLeast (o334SourceU_wc ⟨7, by omega⟩) 15 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 98) o141W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 98) hP hQ o141W_wc 15
      step109_orbit141_lb15_wc
  exact quotientRankAtLeast_mono step109wc334s7_contain hAct

private def step109wc334s8SrcT : Submodule F2 Mat3 := spanCodes [258, 128, 84, 8, 1]

private theorem step109wc334s8SrcT_lb : QuotientRankAtLeast step109wc334s8SrcT 15 := by
  have ht := quotientRankAtLeast_transpose step109_orbit141_lb15_wc
  have hle : step109wc334s8SrcT ≤ transposeW o141W_wc := by
    unfold step109wc334s8SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4
    · subst h0
      show codeMat 258 ∈ Submodule.map transposeLinearMap o141W_wc
      exact ⟨codeMat 264, spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 264 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 128 ∈ Submodule.map transposeLinearMap o141W_wc
      exact ⟨codeMat 32, spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 32 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 84 ∈ Submodule.map transposeLinearMap o141W_wc
      exact ⟨codeMat 84, spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 84 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 8 ∈ Submodule.map transposeLinearMap o141W_wc
      exact ⟨codeMat 2, spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 2 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 1 ∈ Submodule.map transposeLinearMap o141W_wc
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc334s8_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc334s8_contain :
    (o334SourceU_wc ⟨8, by omega⟩) ≤ actionW (codeMat 161) (codeMat 273) step109wc334s8SrcT := by
  change spanCodes [140, 64, 34, 16, 1] ≤ actionW (codeMat 161) (codeMat 273) step109wc334s8SrcT
  apply step109wc334_spanCodes_le_of_gens [140, 64, 34, 16, 1]
    (actionW (codeMat 161) (codeMat 273) step109wc334s8SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 84 ∈ step109wc334s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 8, 1] 84 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 84) = codeMat 140 := by
      unfold actionA
      rw [step109wc334s8_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 84 * (codeMat 273 : Mat3).transpose = codeMat 140
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 8 ∈ step109wc334s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 8, 1] 8 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 8) = codeMat 64 := by
      unfold actionA
      rw [step109wc334s8_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 8 * (codeMat 273 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 258 ∈ step109wc334s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 8, 1] 258 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 258) = codeMat 34 := by
      unfold actionA
      rw [step109wc334s8_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 258 * (codeMat 273 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 128 ∈ step109wc334s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 8, 1] 128 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 128) = codeMat 16 := by
      unfold actionA
      rw [step109wc334s8_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 128 * (codeMat 273 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ step109wc334s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 8, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc334s8_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact

theorem step109wc334s8Dispatch :
    QuotientRankAtLeast (o334SourceU_wc ⟨8, by omega⟩) 15 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 273) step109wc334s8SrcT) 15 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 273) hP hQ step109wc334s8SrcT 15
      step109wc334s8SrcT_lb
  exact quotientRankAtLeast_mono step109wc334s8_contain hAct


private theorem step109wc334s9_QtInv :
    (codeMat 354 : Mat3).transpose⁻¹ = (codeMat 142 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 354 : Mat3).transpose * (codeMat 142 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc334s9_contain :
    (o334SourceU_wc ⟨9, by omega⟩) ≤ actionW (codeMat 394) (codeMat 354) o141W_wc := by
  change spanCodes [140, 74, 40, 16, 1] ≤ actionW (codeMat 394) (codeMat 354) o141W_wc
  apply step109wc334_spanCodes_le_of_gens [140, 74, 40, 16, 1]
    (actionW (codeMat 394) (codeMat 354) o141W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 117 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 117 (by decide)
    have hact : actionA (codeMat 394) (codeMat 354) (codeMat 117) = codeMat 140 := by
      unfold actionA
      rw [step109wc334s9_QtInv]
      show (codeMat 394 : Mat3).transpose * codeMat 117 * (codeMat 142 : Mat3).transpose = codeMat 140
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 264 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 264 (by decide)
    have hact : actionA (codeMat 394) (codeMat 354) (codeMat 264) = codeMat 74 := by
      unfold actionA
      rw [step109wc334s9_QtInv]
      show (codeMat 394 : Mat3).transpose * codeMat 264 * (codeMat 142 : Mat3).transpose = codeMat 74
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 394) (codeMat 354) (codeMat 2) = codeMat 40 := by
      unfold actionA
      rw [step109wc334s9_QtInv]
      show (codeMat 394 : Mat3).transpose * codeMat 2 * (codeMat 142 : Mat3).transpose = codeMat 40
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 394) (codeMat 354) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step109wc334s9_QtInv]
      show (codeMat 394 : Mat3).transpose * codeMat 1 * (codeMat 142 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 32 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 394) (codeMat 354) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step109wc334s9_QtInv]
      show (codeMat 394 : Mat3).transpose * codeMat 32 * (codeMat 142 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact

theorem step109wc334s9Dispatch :
    QuotientRankAtLeast (o334SourceU_wc ⟨9, by omega⟩) 15 := by
  have hP : Invertible (codeMat 394 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 354 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 394) (codeMat 354) o141W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 394) (codeMat 354) hP hQ o141W_wc 15
      step109_orbit141_lb15_wc
  exact quotientRankAtLeast_mono step109wc334s9_contain hAct

private def step109wc334s10SrcT : Submodule F2 Mat3 := spanCodes [258, 128, 84, 8, 1]

private theorem step109wc334s10SrcT_lb : QuotientRankAtLeast step109wc334s10SrcT 15 := by
  have ht := quotientRankAtLeast_transpose step109_orbit141_lb15_wc
  have hle : step109wc334s10SrcT ≤ transposeW o141W_wc := by
    unfold step109wc334s10SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4
    · subst h0
      show codeMat 258 ∈ Submodule.map transposeLinearMap o141W_wc
      exact ⟨codeMat 264, spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 264 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 128 ∈ Submodule.map transposeLinearMap o141W_wc
      exact ⟨codeMat 32, spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 32 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 84 ∈ Submodule.map transposeLinearMap o141W_wc
      exact ⟨codeMat 84, spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 84 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 8 ∈ Submodule.map transposeLinearMap o141W_wc
      exact ⟨codeMat 2, spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 2 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 1 ∈ Submodule.map transposeLinearMap o141W_wc
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc334s10_QtInv :
    (codeMat 277 : Mat3).transpose⁻¹ = (codeMat 277 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 277 : Mat3).transpose * (codeMat 277 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc334s10_contain :
    (o334SourceU_wc ⟨10, by omega⟩) ≤ actionW (codeMat 177) (codeMat 277) step109wc334s10SrcT := by
  change spanCodes [140, 72, 42, 16, 1] ≤ actionW (codeMat 177) (codeMat 277) step109wc334s10SrcT
  apply step109wc334_spanCodes_le_of_gens [140, 72, 42, 16, 1]
    (actionW (codeMat 177) (codeMat 277) step109wc334s10SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 213 ∈ step109wc334s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 8, 1] 213 (by decide)
    have hact : actionA (codeMat 177) (codeMat 277) (codeMat 213) = codeMat 140 := by
      unfold actionA
      rw [step109wc334s10_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 213 * (codeMat 277 : Mat3).transpose = codeMat 140
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 8 ∈ step109wc334s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 8, 1] 8 (by decide)
    have hact : actionA (codeMat 177) (codeMat 277) (codeMat 8) = codeMat 72 := by
      unfold actionA
      rw [step109wc334s10_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 8 * (codeMat 277 : Mat3).transpose = codeMat 72
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 258 ∈ step109wc334s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 8, 1] 258 (by decide)
    have hact : actionA (codeMat 177) (codeMat 277) (codeMat 258) = codeMat 42 := by
      unfold actionA
      rw [step109wc334s10_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 258 * (codeMat 277 : Mat3).transpose = codeMat 42
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 128 ∈ step109wc334s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 8, 1] 128 (by decide)
    have hact : actionA (codeMat 177) (codeMat 277) (codeMat 128) = codeMat 16 := by
      unfold actionA
      rw [step109wc334s10_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 128 * (codeMat 277 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ step109wc334s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 8, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 277) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc334s10_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * (codeMat 277 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact

theorem step109wc334s10Dispatch :
    QuotientRankAtLeast (o334SourceU_wc ⟨10, by omega⟩) 15 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 277 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 277) step109wc334s10SrcT) 15 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 277) hP hQ step109wc334s10SrcT 15
      step109wc334s10SrcT_lb
  exact quotientRankAtLeast_mono step109wc334s10_contain hAct


private theorem step109wc334s11_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc334s11_contain :
    (o334SourceU_wc ⟨11, by omega⟩) ≤ actionW (codeMat 84) (codeMat 84) o231W := by
  change spanCodes [256, 140, 98, 16, 1] ≤ actionW (codeMat 84) (codeMat 84) o231W
  apply step109wc334_spanCodes_le_of_gens [256, 140, 98, 16, 1]
    (actionW (codeMat 84) (codeMat 84) o231W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 1 ∈ o231W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 140, 98, 16, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step109wc334s11_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 84 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 98 ∈ o231W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 140, 98, 16, 1] 98 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 98) = codeMat 140 := by
      unfold actionA
      rw [step109wc334s11_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 98 * (codeMat 84 : Mat3).transpose = codeMat 140
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 140 ∈ o231W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 140, 98, 16, 1] 140 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 140) = codeMat 98 := by
      unfold actionA
      rw [step109wc334s11_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 140 * (codeMat 84 : Mat3).transpose = codeMat 98
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 16 ∈ o231W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 140, 98, 16, 1] 16 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 16) = codeMat 16 := by
      unfold actionA
      rw [step109wc334s11_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 16 * (codeMat 84 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 256 ∈ o231W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 140, 98, 16, 1] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc334s11_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 84 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact

theorem step109wc334s11Dispatch :
    QuotientRankAtLeast (o334SourceU_wc ⟨11, by omega⟩) 15 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 84) o231W) 15 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 84) hP hQ o231W 15
      step99_orbit231_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc334s11_contain hAct


private theorem step109wc334s12_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc334s12_contain :
    (o334SourceU_wc ⟨12, by omega⟩) ≤ actionW (codeMat 273) (codeMat 273) o232W_mono := by
  change spanCodes [258, 140, 98, 16, 1] ≤ actionW (codeMat 273) (codeMat 273) o232W_mono
  apply step109wc334_spanCodes_le_of_gens [258, 140, 98, 16, 1]
    (actionW (codeMat 273) (codeMat 273) o232W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 258 ∈ o232W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 140, 98, 16, 1] 258 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 258) = codeMat 258 := by
      unfold actionA
      rw [step109wc334s12_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 258 * (codeMat 273 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 140 ∈ o232W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 140, 98, 16, 1] 140 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 140) = codeMat 140 := by
      unfold actionA
      rw [step109wc334s12_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 140 * (codeMat 273 : Mat3).transpose = codeMat 140
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 98 ∈ o232W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 140, 98, 16, 1] 98 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 98) = codeMat 98 := by
      unfold actionA
      rw [step109wc334s12_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 98 * (codeMat 273 : Mat3).transpose = codeMat 98
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 16 ∈ o232W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 140, 98, 16, 1] 16 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 16) = codeMat 16 := by
      unfold actionA
      rw [step109wc334s12_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 16 * (codeMat 273 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o232W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 140, 98, 16, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc334s12_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact

theorem step109wc334s12Dispatch :
    QuotientRankAtLeast (o334SourceU_wc ⟨12, by omega⟩) 15 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 273) o232W_mono) 15 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 273) hP hQ o232W_mono 15
      orbit232_lb15_mono
  exact quotientRankAtLeast_mono step109wc334s12_contain hAct


private theorem step109wc334s13_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc334s13_contain :
    (o334SourceU_wc ⟨13, by omega⟩) ≤ actionW (codeMat 273) (codeMat 273) o233W_wc := by
  change spanCodes [260, 140, 98, 16, 1] ≤ actionW (codeMat 273) (codeMat 273) o233W_wc
  apply step109wc334_spanCodes_le_of_gens [260, 140, 98, 16, 1]
    (actionW (codeMat 273) (codeMat 273) o233W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 260 ∈ o233W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] 260 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 260) = codeMat 260 := by
      unfold actionA
      rw [step109wc334s13_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 260 * (codeMat 273 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 140 ∈ o233W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] 140 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 140) = codeMat 140 := by
      unfold actionA
      rw [step109wc334s13_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 140 * (codeMat 273 : Mat3).transpose = codeMat 140
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 98 ∈ o233W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] 98 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 98) = codeMat 98 := by
      unfold actionA
      rw [step109wc334s13_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 98 * (codeMat 273 : Mat3).transpose = codeMat 98
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 16 ∈ o233W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] 16 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 16) = codeMat 16 := by
      unfold actionA
      rw [step109wc334s13_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 16 * (codeMat 273 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o233W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc334s13_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact

theorem step109wc334s13Dispatch :
    QuotientRankAtLeast (o334SourceU_wc ⟨13, by omega⟩) 15 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 273) o233W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 273) hP hQ o233W_wc 15
      step109_orbit233_lb15_wc
  exact quotientRankAtLeast_mono step109wc334s13_contain hAct


private theorem step109wc334s14_QtInv :
    (codeMat 309 : Mat3).transpose⁻¹ = (codeMat 309 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 309 : Mat3).transpose * (codeMat 309 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc334s14_contain :
    (o334SourceU_wc ⟨14, by omega⟩) ≤ actionW (codeMat 465) (codeMat 309) o233W_wc := by
  change spanCodes [262, 140, 98, 16, 1] ≤ actionW (codeMat 465) (codeMat 309) o233W_wc
  apply step109wc334_spanCodes_le_of_gens [262, 140, 98, 16, 1]
    (actionW (codeMat 465) (codeMat 309) o233W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 506 ∈ o233W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] 506 (by decide)
    have hact : actionA (codeMat 465) (codeMat 309) (codeMat 506) = codeMat 262 := by
      unfold actionA
      rw [step109wc334s14_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 506 * (codeMat 309 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 157 ∈ o233W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] 157 (by decide)
    have hact : actionA (codeMat 465) (codeMat 309) (codeMat 157) = codeMat 140 := by
      unfold actionA
      rw [step109wc334s14_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 157 * (codeMat 309 : Mat3).transpose = codeMat 140
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 115 ∈ o233W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] 115 (by decide)
    have hact : actionA (codeMat 465) (codeMat 309) (codeMat 115) = codeMat 98 := by
      unfold actionA
      rw [step109wc334s14_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 115 * (codeMat 309 : Mat3).transpose = codeMat 98
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 16 ∈ o233W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] 16 (by decide)
    have hact : actionA (codeMat 465) (codeMat 309) (codeMat 16) = codeMat 16 := by
      unfold actionA
      rw [step109wc334s14_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 16 * (codeMat 309 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o233W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] 1 (by decide)
    have hact : actionA (codeMat 465) (codeMat 309) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc334s14_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 1 * (codeMat 309 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact

theorem step109wc334s14Dispatch :
    QuotientRankAtLeast (o334SourceU_wc ⟨14, by omega⟩) 15 := by
  have hP : Invertible (codeMat 465 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 309 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 465) (codeMat 309) o233W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 465) (codeMat 309) hP hQ o233W_wc 15
      step109_orbit233_lb15_wc
  exact quotientRankAtLeast_mono step109wc334s14_contain hAct


private theorem step109wc334s15_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc334s15_contain :
    (o334SourceU_wc ⟨15, by omega⟩) ≤ actionW (codeMat 266) (codeMat 266) o232W_mono := by
  change spanCodes [264, 140, 98, 16, 1] ≤ actionW (codeMat 266) (codeMat 266) o232W_mono
  apply step109wc334_spanCodes_le_of_gens [264, 140, 98, 16, 1]
    (actionW (codeMat 266) (codeMat 266) o232W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 258 ∈ o232W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 140, 98, 16, 1] 258 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 258) = codeMat 264 := by
      unfold actionA
      rw [step109wc334s15_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 258 * (codeMat 266 : Mat3).transpose = codeMat 264
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 98 ∈ o232W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 140, 98, 16, 1] 98 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 98) = codeMat 140 := by
      unfold actionA
      rw [step109wc334s15_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 98 * (codeMat 266 : Mat3).transpose = codeMat 140
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 140 ∈ o232W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 140, 98, 16, 1] 140 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 140) = codeMat 98 := by
      unfold actionA
      rw [step109wc334s15_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 140 * (codeMat 266 : Mat3).transpose = codeMat 98
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o232W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 140, 98, 16, 1] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step109wc334s15_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 16 ∈ o232W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 140, 98, 16, 1] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc334s15_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact

theorem step109wc334s15Dispatch :
    QuotientRankAtLeast (o334SourceU_wc ⟨15, by omega⟩) 15 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 266) o232W_mono) 15 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 266) hP hQ o232W_mono 15
      orbit232_lb15_mono
  exact quotientRankAtLeast_mono step109wc334s15_contain hAct


private theorem step109wc334s16_QtInv :
    (codeMat 116 : Mat3).transpose⁻¹ = (codeMat 92 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 116 : Mat3).transpose * (codeMat 92 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc334s16_contain :
    (o334SourceU_wc ⟨16, by omega⟩) ≤ actionW (codeMat 85) (codeMat 116) o231W := by
  change spanCodes [266, 140, 98, 16, 1] ≤ actionW (codeMat 85) (codeMat 116) o231W
  apply step109wc334_spanCodes_le_of_gens [266, 140, 98, 16, 1]
    (actionW (codeMat 85) (codeMat 116) o231W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 99 ∈ o231W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 140, 98, 16, 1] 99 (by decide)
    have hact : actionA (codeMat 85) (codeMat 116) (codeMat 99) = codeMat 266 := by
      unfold actionA
      rw [step109wc334s16_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 99 * (codeMat 92 : Mat3).transpose = codeMat 266
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 98 ∈ o231W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 140, 98, 16, 1] 98 (by decide)
    have hact : actionA (codeMat 85) (codeMat 116) (codeMat 98) = codeMat 140 := by
      unfold actionA
      rw [step109wc334s16_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 98 * (codeMat 92 : Mat3).transpose = codeMat 140
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 412 ∈ o231W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 140, 98, 16, 1] 412 (by decide)
    have hact : actionA (codeMat 85) (codeMat 116) (codeMat 412) = codeMat 98 := by
      unfold actionA
      rw [step109wc334s16_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 412 * (codeMat 92 : Mat3).transpose = codeMat 98
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 16 ∈ o231W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 140, 98, 16, 1] 16 (by decide)
    have hact : actionA (codeMat 85) (codeMat 116) (codeMat 16) = codeMat 16 := by
      unfold actionA
      rw [step109wc334s16_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 16 * (codeMat 92 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 256 ∈ o231W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 140, 98, 16, 1] 256 (by decide)
    have hact : actionA (codeMat 85) (codeMat 116) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc334s16_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 256 * (codeMat 92 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact

theorem step109wc334s16Dispatch :
    QuotientRankAtLeast (o334SourceU_wc ⟨16, by omega⟩) 15 := by
  have hP : Invertible (codeMat 85 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 116 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 85) (codeMat 116) o231W) 15 :=
    @quotientRankAtLeast_action (codeMat 85) (codeMat 116) hP hQ o231W 15
      step99_orbit231_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc334s16_contain hAct


private theorem step109wc334s17_QtInv :
    (codeMat 305 : Mat3).transpose⁻¹ = (codeMat 305 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 305 : Mat3).transpose * (codeMat 305 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc334s17_contain :
    (o334SourceU_wc ⟨17, by omega⟩) ≤ actionW (codeMat 337) (codeMat 305) o233W_wc := by
  change spanCodes [268, 140, 98, 16, 1] ≤ actionW (codeMat 337) (codeMat 305) o233W_wc
  apply step109wc334_spanCodes_le_of_gens [268, 140, 98, 16, 1]
    (actionW (codeMat 337) (codeMat 305) o233W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 392 ∈ o233W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] 392 (by decide)
    have hact : actionA (codeMat 337) (codeMat 305) (codeMat 392) = codeMat 268 := by
      unfold actionA
      rw [step109wc334s17_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 392 * (codeMat 305 : Mat3).transpose = codeMat 268
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 140 ∈ o233W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] 140 (by decide)
    have hact : actionA (codeMat 337) (codeMat 305) (codeMat 140) = codeMat 140 := by
      unfold actionA
      rw [step109wc334s17_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 140 * (codeMat 305 : Mat3).transpose = codeMat 140
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 115 ∈ o233W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] 115 (by decide)
    have hact : actionA (codeMat 337) (codeMat 305) (codeMat 115) = codeMat 98 := by
      unfold actionA
      rw [step109wc334s17_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 115 * (codeMat 305 : Mat3).transpose = codeMat 98
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 16 ∈ o233W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] 16 (by decide)
    have hact : actionA (codeMat 337) (codeMat 305) (codeMat 16) = codeMat 16 := by
      unfold actionA
      rw [step109wc334s17_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 16 * (codeMat 305 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o233W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] 1 (by decide)
    have hact : actionA (codeMat 337) (codeMat 305) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc334s17_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 1 * (codeMat 305 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact

theorem step109wc334s17Dispatch :
    QuotientRankAtLeast (o334SourceU_wc ⟨17, by omega⟩) 15 := by
  have hP : Invertible (codeMat 337 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 337) (codeMat 305) o233W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 337) (codeMat 305) hP hQ o233W_wc 15
      step109_orbit233_lb15_wc
  exact quotientRankAtLeast_mono step109wc334s17_contain hAct


private theorem step109wc334s18_QtInv :
    (codeMat 277 : Mat3).transpose⁻¹ = (codeMat 277 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 277 : Mat3).transpose * (codeMat 277 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc334s18_contain :
    (o334SourceU_wc ⟨18, by omega⟩) ≤ actionW (codeMat 401) (codeMat 277) o233W_wc := by
  change spanCodes [270, 140, 98, 16, 1] ≤ actionW (codeMat 401) (codeMat 277) o233W_wc
  apply step109wc334_spanCodes_le_of_gens [270, 140, 98, 16, 1]
    (actionW (codeMat 401) (codeMat 277) o233W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 359 ∈ o233W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] 359 (by decide)
    have hact : actionA (codeMat 401) (codeMat 277) (codeMat 359) = codeMat 270 := by
      unfold actionA
      rw [step109wc334s18_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 359 * (codeMat 277 : Mat3).transpose = codeMat 270
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 157 ∈ o233W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] 157 (by decide)
    have hact : actionA (codeMat 401) (codeMat 277) (codeMat 157) = codeMat 140 := by
      unfold actionA
      rw [step109wc334s18_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 157 * (codeMat 277 : Mat3).transpose = codeMat 140
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 98 ∈ o233W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] 98 (by decide)
    have hact : actionA (codeMat 401) (codeMat 277) (codeMat 98) = codeMat 98 := by
      unfold actionA
      rw [step109wc334s18_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 98 * (codeMat 277 : Mat3).transpose = codeMat 98
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 16 ∈ o233W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] 16 (by decide)
    have hact : actionA (codeMat 401) (codeMat 277) (codeMat 16) = codeMat 16 := by
      unfold actionA
      rw [step109wc334s18_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 16 * (codeMat 277 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o233W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] 1 (by decide)
    have hact : actionA (codeMat 401) (codeMat 277) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc334s18_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 1 * (codeMat 277 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact

theorem step109wc334s18Dispatch :
    QuotientRankAtLeast (o334SourceU_wc ⟨18, by omega⟩) 15 := by
  have hP : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 277 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 401) (codeMat 277) o233W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 401) (codeMat 277) hP hQ o233W_wc 15
      step109_orbit233_lb15_wc
  exact quotientRankAtLeast_mono step109wc334s18_contain hAct


private theorem step109wc334s19_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc334s19_contain :
    (o334SourceU_wc ⟨19, by omega⟩) ≤ actionW (codeMat 266) (codeMat 266) o233W_wc := by
  change spanCodes [288, 140, 98, 16, 1] ≤ actionW (codeMat 266) (codeMat 266) o233W_wc
  apply step109wc334_spanCodes_le_of_gens [288, 140, 98, 16, 1]
    (actionW (codeMat 266) (codeMat 266) o233W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 260 ∈ o233W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] 260 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 260) = codeMat 288 := by
      unfold actionA
      rw [step109wc334s19_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 260 * (codeMat 266 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 98 ∈ o233W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] 98 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 98) = codeMat 140 := by
      unfold actionA
      rw [step109wc334s19_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 98 * (codeMat 266 : Mat3).transpose = codeMat 140
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 140 ∈ o233W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] 140 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 140) = codeMat 98 := by
      unfold actionA
      rw [step109wc334s19_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 140 * (codeMat 266 : Mat3).transpose = codeMat 98
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o233W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step109wc334s19_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 16 ∈ o233W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc334s19_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact

theorem step109wc334s19Dispatch :
    QuotientRankAtLeast (o334SourceU_wc ⟨19, by omega⟩) 15 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 266) o233W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 266) hP hQ o233W_wc 15
      step109_orbit233_lb15_wc
  exact quotientRankAtLeast_mono step109wc334s19_contain hAct


private theorem step109wc334s20_QtInv :
    (codeMat 298 : Mat3).transpose⁻¹ = (codeMat 270 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 298 : Mat3).transpose * (codeMat 270 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc334s20_contain :
    (o334SourceU_wc ⟨20, by omega⟩) ≤ actionW (codeMat 394) (codeMat 298) o233W_wc := by
  change spanCodes [290, 140, 98, 16, 1] ≤ actionW (codeMat 394) (codeMat 298) o233W_wc
  apply step109wc334_spanCodes_le_of_gens [290, 140, 98, 16, 1]
    (actionW (codeMat 394) (codeMat 298) o233W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 392 ∈ o233W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] 392 (by decide)
    have hact : actionA (codeMat 394) (codeMat 298) (codeMat 392) = codeMat 290 := by
      unfold actionA
      rw [step109wc334s20_QtInv]
      show (codeMat 394 : Mat3).transpose * codeMat 392 * (codeMat 270 : Mat3).transpose = codeMat 290
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 115 ∈ o233W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] 115 (by decide)
    have hact : actionA (codeMat 394) (codeMat 298) (codeMat 115) = codeMat 140 := by
      unfold actionA
      rw [step109wc334s20_QtInv]
      show (codeMat 394 : Mat3).transpose * codeMat 115 * (codeMat 270 : Mat3).transpose = codeMat 140
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 140 ∈ o233W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] 140 (by decide)
    have hact : actionA (codeMat 394) (codeMat 298) (codeMat 140) = codeMat 98 := by
      unfold actionA
      rw [step109wc334s20_QtInv]
      show (codeMat 394 : Mat3).transpose * codeMat 140 * (codeMat 270 : Mat3).transpose = codeMat 98
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o233W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] 1 (by decide)
    have hact : actionA (codeMat 394) (codeMat 298) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step109wc334s20_QtInv]
      show (codeMat 394 : Mat3).transpose * codeMat 1 * (codeMat 270 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 16 ∈ o233W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] 16 (by decide)
    have hact : actionA (codeMat 394) (codeMat 298) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc334s20_QtInv]
      show (codeMat 394 : Mat3).transpose * codeMat 16 * (codeMat 270 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact

theorem step109wc334s20Dispatch :
    QuotientRankAtLeast (o334SourceU_wc ⟨20, by omega⟩) 15 := by
  have hP : Invertible (codeMat 394 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 298 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 394) (codeMat 298) o233W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 394) (codeMat 298) hP hQ o233W_wc 15
      step109_orbit233_lb15_wc
  exact quotientRankAtLeast_mono step109wc334s20_contain hAct


private theorem step109wc334s21_QtInv :
    (codeMat 204 : Mat3).transpose⁻¹ = (codeMat 114 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 204 : Mat3).transpose * (codeMat 114 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc334s21_contain :
    (o334SourceU_wc ⟨21, by omega⟩) ≤ actionW (codeMat 95) (codeMat 204) o209W_mono := by
  change spanCodes [292, 140, 98, 16, 1] ≤ actionW (codeMat 95) (codeMat 204) o209W_mono
  apply step109wc334_spanCodes_le_of_gens [292, 140, 98, 16, 1]
    (actionW (codeMat 95) (codeMat 204) o209W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 1 ∈ o209W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 84, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 95) (codeMat 204) (codeMat 1) = codeMat 292 := by
      unfold actionA
      rw [step109wc334s21_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 1 * (codeMat 114 : Mat3).transpose = codeMat 292
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 468 ∈ o209W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 84, 10, 1] 468 (by decide)
    have hact : actionA (codeMat 95) (codeMat 204) (codeMat 468) = codeMat 140 := by
      unfold actionA
      rw [step109wc334s21_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 468 * (codeMat 114 : Mat3).transpose = codeMat 140
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 382 ∈ o209W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 84, 10, 1] 382 (by decide)
    have hact : actionA (codeMat 95) (codeMat 204) (codeMat 382) = codeMat 98 := by
      unfold actionA
      rw [step109wc334s21_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 382 * (codeMat 114 : Mat3).transpose = codeMat 98
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 288 ∈ o209W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 84, 10, 1] 288 (by decide)
    have hact : actionA (codeMat 95) (codeMat 204) (codeMat 288) = codeMat 16 := by
      unfold actionA
      rw [step109wc334s21_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 288 * (codeMat 114 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 384 ∈ o209W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 84, 10, 1] 384 (by decide)
    have hact : actionA (codeMat 95) (codeMat 204) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step109wc334s21_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 384 * (codeMat 114 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact

theorem step109wc334s21Dispatch :
    QuotientRankAtLeast (o334SourceU_wc ⟨21, by omega⟩) 15 := by
  have hP : Invertible (codeMat 95 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 204 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 95) (codeMat 204) o209W_mono) 15 :=
    @quotientRankAtLeast_action (codeMat 95) (codeMat 204) hP hQ o209W_mono 15
      orbit209_lb15_mono
  exact quotientRankAtLeast_mono step109wc334s21_contain hAct


private theorem step109wc334s22_QtInv :
    (codeMat 492 : Mat3).transpose⁻¹ = (codeMat 115 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 492 : Mat3).transpose * (codeMat 115 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc334s22_contain :
    (o334SourceU_wc ⟨22, by omega⟩) ≤ actionW (codeMat 93) (codeMat 492) o209W_mono := by
  change spanCodes [294, 140, 98, 16, 1] ≤ actionW (codeMat 93) (codeMat 492) o209W_mono
  apply step109wc334_spanCodes_le_of_gens [294, 140, 98, 16, 1]
    (actionW (codeMat 93) (codeMat 492) o209W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 255 ∈ o209W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 84, 10, 1] 255 (by decide)
    have hact : actionA (codeMat 93) (codeMat 492) (codeMat 255) = codeMat 294 := by
      unfold actionA
      rw [step109wc334s22_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 255 * (codeMat 115 : Mat3).transpose = codeMat 294
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 372 ∈ o209W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 84, 10, 1] 372 (by decide)
    have hact : actionA (codeMat 93) (codeMat 492) (codeMat 372) = codeMat 140 := by
      unfold actionA
      rw [step109wc334s22_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 372 * (codeMat 115 : Mat3).transpose = codeMat 140
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 382 ∈ o209W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 84, 10, 1] 382 (by decide)
    have hact : actionA (codeMat 93) (codeMat 492) (codeMat 382) = codeMat 98 := by
      unfold actionA
      rw [step109wc334s22_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 382 * (codeMat 115 : Mat3).transpose = codeMat 98
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 288 ∈ o209W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 84, 10, 1] 288 (by decide)
    have hact : actionA (codeMat 93) (codeMat 492) (codeMat 288) = codeMat 16 := by
      unfold actionA
      rw [step109wc334s22_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 288 * (codeMat 115 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 384 ∈ o209W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 84, 10, 1] 384 (by decide)
    have hact : actionA (codeMat 93) (codeMat 492) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step109wc334s22_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 384 * (codeMat 115 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact

theorem step109wc334s22Dispatch :
    QuotientRankAtLeast (o334SourceU_wc ⟨22, by omega⟩) 15 := by
  have hP : Invertible (codeMat 93 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 492 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 93) (codeMat 492) o209W_mono) 15 :=
    @quotientRankAtLeast_action (codeMat 93) (codeMat 492) hP hQ o209W_mono 15
      orbit209_lb15_mono
  exact quotientRankAtLeast_mono step109wc334s22_contain hAct


private theorem step109wc334s23_QtInv :
    (codeMat 302 : Mat3).transpose⁻¹ = (codeMat 302 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 302 : Mat3).transpose * (codeMat 302 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc334s23_contain :
    (o334SourceU_wc ⟨23, by omega⟩) ≤ actionW (codeMat 458) (codeMat 302) o233W_wc := by
  change spanCodes [296, 140, 98, 16, 1] ≤ actionW (codeMat 458) (codeMat 302) o233W_wc
  apply step109wc334_spanCodes_le_of_gens [296, 140, 98, 16, 1]
    (actionW (codeMat 458) (codeMat 302) o233W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 506 ∈ o233W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] 506 (by decide)
    have hact : actionA (codeMat 458) (codeMat 302) (codeMat 506) = codeMat 296 := by
      unfold actionA
      rw [step109wc334s23_QtInv]
      show (codeMat 458 : Mat3).transpose * codeMat 506 * (codeMat 302 : Mat3).transpose = codeMat 296
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 115 ∈ o233W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] 115 (by decide)
    have hact : actionA (codeMat 458) (codeMat 302) (codeMat 115) = codeMat 140 := by
      unfold actionA
      rw [step109wc334s23_QtInv]
      show (codeMat 458 : Mat3).transpose * codeMat 115 * (codeMat 302 : Mat3).transpose = codeMat 140
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 157 ∈ o233W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] 157 (by decide)
    have hact : actionA (codeMat 458) (codeMat 302) (codeMat 157) = codeMat 98 := by
      unfold actionA
      rw [step109wc334s23_QtInv]
      show (codeMat 458 : Mat3).transpose * codeMat 157 * (codeMat 302 : Mat3).transpose = codeMat 98
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o233W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] 1 (by decide)
    have hact : actionA (codeMat 458) (codeMat 302) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step109wc334s23_QtInv]
      show (codeMat 458 : Mat3).transpose * codeMat 1 * (codeMat 302 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 16 ∈ o233W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] 16 (by decide)
    have hact : actionA (codeMat 458) (codeMat 302) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc334s23_QtInv]
      show (codeMat 458 : Mat3).transpose * codeMat 16 * (codeMat 302 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact

theorem step109wc334s23Dispatch :
    QuotientRankAtLeast (o334SourceU_wc ⟨23, by omega⟩) 15 := by
  have hP : Invertible (codeMat 458 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 302 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 458) (codeMat 302) o233W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 458) (codeMat 302) hP hQ o233W_wc 15
      step109_orbit233_lb15_wc
  exact quotientRankAtLeast_mono step109wc334s23_contain hAct


private theorem step109wc334s24_QtInv :
    (codeMat 270 : Mat3).transpose⁻¹ = (codeMat 298 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 270 : Mat3).transpose * (codeMat 298 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc334s24_contain :
    (o334SourceU_wc ⟨24, by omega⟩) ≤ actionW (codeMat 330) (codeMat 270) o233W_wc := by
  change spanCodes [298, 140, 98, 16, 1] ≤ actionW (codeMat 330) (codeMat 270) o233W_wc
  apply step109wc334_spanCodes_le_of_gens [298, 140, 98, 16, 1]
    (actionW (codeMat 330) (codeMat 270) o233W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 359 ∈ o233W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] 359 (by decide)
    have hact : actionA (codeMat 330) (codeMat 270) (codeMat 359) = codeMat 298 := by
      unfold actionA
      rw [step109wc334s24_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 359 * (codeMat 298 : Mat3).transpose = codeMat 298
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 98 ∈ o233W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] 98 (by decide)
    have hact : actionA (codeMat 330) (codeMat 270) (codeMat 98) = codeMat 140 := by
      unfold actionA
      rw [step109wc334s24_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 98 * (codeMat 298 : Mat3).transpose = codeMat 140
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 157 ∈ o233W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] 157 (by decide)
    have hact : actionA (codeMat 330) (codeMat 270) (codeMat 157) = codeMat 98 := by
      unfold actionA
      rw [step109wc334s24_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 157 * (codeMat 298 : Mat3).transpose = codeMat 98
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o233W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] 1 (by decide)
    have hact : actionA (codeMat 330) (codeMat 270) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step109wc334s24_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 1 * (codeMat 298 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 16 ∈ o233W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] 16 (by decide)
    have hact : actionA (codeMat 330) (codeMat 270) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc334s24_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 16 * (codeMat 298 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact

theorem step109wc334s24Dispatch :
    QuotientRankAtLeast (o334SourceU_wc ⟨24, by omega⟩) 15 := by
  have hP : Invertible (codeMat 330 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 270 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 330) (codeMat 270) o233W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 330) (codeMat 270) hP hQ o233W_wc 15
      step109_orbit233_lb15_wc
  exact quotientRankAtLeast_mono step109wc334s24_contain hAct


private theorem step109wc334s25_QtInv :
    (codeMat 460 : Mat3).transpose⁻¹ = (codeMat 122 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 460 : Mat3).transpose * (codeMat 122 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc334s25_contain :
    (o334SourceU_wc ⟨25, by omega⟩) ≤ actionW (codeMat 94) (codeMat 460) o209W_mono := by
  change spanCodes [300, 140, 98, 16, 1] ≤ actionW (codeMat 94) (codeMat 460) o209W_mono
  apply step109wc334_spanCodes_le_of_gens [300, 140, 98, 16, 1]
    (actionW (codeMat 94) (codeMat 460) o209W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 245 ∈ o209W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 84, 10, 1] 245 (by decide)
    have hact : actionA (codeMat 94) (codeMat 460) (codeMat 245) = codeMat 300 := by
      unfold actionA
      rw [step109wc334s25_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 245 * (codeMat 122 : Mat3).transpose = codeMat 300
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 468 ∈ o209W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 84, 10, 1] 468 (by decide)
    have hact : actionA (codeMat 94) (codeMat 460) (codeMat 468) = codeMat 140 := by
      unfold actionA
      rw [step109wc334s25_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 468 * (codeMat 122 : Mat3).transpose = codeMat 140
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 478 ∈ o209W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 84, 10, 1] 478 (by decide)
    have hact : actionA (codeMat 94) (codeMat 460) (codeMat 478) = codeMat 98 := by
      unfold actionA
      rw [step109wc334s25_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 478 * (codeMat 122 : Mat3).transpose = codeMat 98
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 288 ∈ o209W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 84, 10, 1] 288 (by decide)
    have hact : actionA (codeMat 94) (codeMat 460) (codeMat 288) = codeMat 16 := by
      unfold actionA
      rw [step109wc334s25_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 288 * (codeMat 122 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 384 ∈ o209W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 84, 10, 1] 384 (by decide)
    have hact : actionA (codeMat 94) (codeMat 460) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step109wc334s25_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 384 * (codeMat 122 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact

theorem step109wc334s25Dispatch :
    QuotientRankAtLeast (o334SourceU_wc ⟨25, by omega⟩) 15 := by
  have hP : Invertible (codeMat 94 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 460 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 94) (codeMat 460) o209W_mono) 15 :=
    @quotientRankAtLeast_action (codeMat 94) (codeMat 460) hP hQ o209W_mono 15
      orbit209_lb15_mono
  exact quotientRankAtLeast_mono step109wc334s25_contain hAct


private theorem step109wc334s26_QtInv :
    (codeMat 236 : Mat3).transpose⁻¹ = (codeMat 123 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 236 : Mat3).transpose * (codeMat 123 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc334s26_contain :
    (o334SourceU_wc ⟨26, by omega⟩) ≤ actionW (codeMat 92) (codeMat 236) o209W_mono := by
  change spanCodes [302, 140, 98, 16, 1] ≤ actionW (codeMat 92) (codeMat 236) o209W_mono
  apply step109wc334_spanCodes_le_of_gens [302, 140, 98, 16, 1]
    (actionW (codeMat 92) (codeMat 236) o209W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 171 ∈ o209W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 84, 10, 1] 171 (by decide)
    have hact : actionA (codeMat 92) (codeMat 236) (codeMat 171) = codeMat 302 := by
      unfold actionA
      rw [step109wc334s26_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 171 * (codeMat 123 : Mat3).transpose = codeMat 302
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 372 ∈ o209W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 84, 10, 1] 372 (by decide)
    have hact : actionA (codeMat 92) (codeMat 236) (codeMat 372) = codeMat 140 := by
      unfold actionA
      rw [step109wc334s26_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 372 * (codeMat 123 : Mat3).transpose = codeMat 140
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 478 ∈ o209W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 84, 10, 1] 478 (by decide)
    have hact : actionA (codeMat 92) (codeMat 236) (codeMat 478) = codeMat 98 := by
      unfold actionA
      rw [step109wc334s26_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 478 * (codeMat 123 : Mat3).transpose = codeMat 98
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 288 ∈ o209W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 84, 10, 1] 288 (by decide)
    have hact : actionA (codeMat 92) (codeMat 236) (codeMat 288) = codeMat 16 := by
      unfold actionA
      rw [step109wc334s26_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 288 * (codeMat 123 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 384 ∈ o209W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 84, 10, 1] 384 (by decide)
    have hact : actionA (codeMat 92) (codeMat 236) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step109wc334s26_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 384 * (codeMat 123 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact

theorem step109wc334s26Dispatch :
    QuotientRankAtLeast (o334SourceU_wc ⟨26, by omega⟩) 15 := by
  have hP : Invertible (codeMat 92 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 236 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 92) (codeMat 236) o209W_mono) 15 :=
    @quotientRankAtLeast_action (codeMat 92) (codeMat 236) hP hQ o209W_mono 15
      orbit209_lb15_mono
  exact quotientRankAtLeast_mono step109wc334s26_contain hAct


private theorem step109wc334s27_QtInv :
    (codeMat 423 : Mat3).transpose⁻¹ = (codeMat 181 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 423 : Mat3).transpose * (codeMat 181 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc334s27_contain :
    (o334SourceU_wc ⟨27, by omega⟩) ≤ actionW (codeMat 233) (codeMat 423) o215W_mono := by
  change spanCodes [140, 70, 36, 16, 1] ≤ actionW (codeMat 233) (codeMat 423) o215W_mono
  apply step109wc334_spanCodes_le_of_gens [140, 70, 36, 16, 1]
    (actionW (codeMat 233) (codeMat 423) o215W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 107 ∈ o215W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 132, 96, 10, 1] 107 (by decide)
    have hact : actionA (codeMat 233) (codeMat 423) (codeMat 107) = codeMat 140 := by
      unfold actionA
      rw [step109wc334s27_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 107 * (codeMat 181 : Mat3).transpose = codeMat 140
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 11 ∈ o215W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 132, 96, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 233) (codeMat 423) (codeMat 11) = codeMat 70 := by
      unfold actionA
      rw [step109wc334s27_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 11 * (codeMat 181 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 448 ∈ o215W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 132, 96, 10, 1] 448 (by decide)
    have hact : actionA (codeMat 233) (codeMat 423) (codeMat 448) = codeMat 36 := by
      unfold actionA
      rw [step109wc334s27_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 448 * (codeMat 181 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 325 ∈ o215W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 132, 96, 10, 1] 325 (by decide)
    have hact : actionA (codeMat 233) (codeMat 423) (codeMat 325) = codeMat 16 := by
      unfold actionA
      rw [step109wc334s27_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 325 * (codeMat 181 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o215W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 132, 96, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 233) (codeMat 423) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc334s27_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 1 * (codeMat 181 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact

theorem step109wc334s27Dispatch :
    QuotientRankAtLeast (o334SourceU_wc ⟨27, by omega⟩) 14 := by
  have hP : Invertible (codeMat 233 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 423 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 233) (codeMat 423) o215W_mono) 14 :=
    @quotientRankAtLeast_action (codeMat 233) (codeMat 423) hP hQ o215W_mono 14
      orbit215_lb14_mono
  exact quotientRankAtLeast_mono step109wc334s27_contain hAct


private theorem step109wc334s28_QtInv :
    (codeMat 163 : Mat3).transpose⁻¹ = (codeMat 165 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 163 : Mat3).transpose * (codeMat 165 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc334s28_contain :
    (o334SourceU_wc ⟨28, by omega⟩) ≤ actionW (codeMat 225) (codeMat 163) o215W_mono := by
  change spanCodes [140, 68, 38, 16, 1] ≤ actionW (codeMat 225) (codeMat 163) o215W_mono
  apply step109wc334_spanCodes_le_of_gens [140, 68, 38, 16, 1]
    (actionW (codeMat 225) (codeMat 163) o215W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 107 ∈ o215W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 132, 96, 10, 1] 107 (by decide)
    have hact : actionA (codeMat 225) (codeMat 163) (codeMat 107) = codeMat 140 := by
      unfold actionA
      rw [step109wc334s28_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 107 * (codeMat 165 : Mat3).transpose = codeMat 140
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 10 ∈ o215W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 132, 96, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 225) (codeMat 163) (codeMat 10) = codeMat 68 := by
      unfold actionA
      rw [step109wc334s28_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 10 * (codeMat 165 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 133 ∈ o215W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 132, 96, 10, 1] 133 (by decide)
    have hact : actionA (codeMat 225) (codeMat 163) (codeMat 133) = codeMat 38 := by
      unfold actionA
      rw [step109wc334s28_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 133 * (codeMat 165 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 325 ∈ o215W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 132, 96, 10, 1] 325 (by decide)
    have hact : actionA (codeMat 225) (codeMat 163) (codeMat 325) = codeMat 16 := by
      unfold actionA
      rw [step109wc334s28_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 325 * (codeMat 165 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o215W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 132, 96, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 225) (codeMat 163) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc334s28_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 1 * (codeMat 165 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact

theorem step109wc334s28Dispatch :
    QuotientRankAtLeast (o334SourceU_wc ⟨28, by omega⟩) 14 := by
  have hP : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 163 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 225) (codeMat 163) o215W_mono) 14 :=
    @quotientRankAtLeast_action (codeMat 225) (codeMat 163) hP hQ o215W_mono 14
      orbit215_lb14_mono
  exact quotientRankAtLeast_mono step109wc334s28_contain hAct


private theorem step109wc334s29_QtInv :
    (codeMat 99 : Mat3).transpose⁻¹ = (codeMat 172 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 99 : Mat3).transpose * (codeMat 172 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc334s29_contain :
    (o334SourceU_wc ⟨29, by omega⟩) ≤ actionW (codeMat 226) (codeMat 99) o215W_mono := by
  change spanCodes [140, 78, 44, 16, 1] ≤ actionW (codeMat 226) (codeMat 99) o215W_mono
  apply step109wc334_spanCodes_le_of_gens [140, 78, 44, 16, 1]
    (actionW (codeMat 226) (codeMat 99) o215W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 143 ∈ o215W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 132, 96, 10, 1] 143 (by decide)
    have hact : actionA (codeMat 226) (codeMat 99) (codeMat 143) = codeMat 140 := by
      unfold actionA
      rw [step109wc334s29_QtInv]
      show (codeMat 226 : Mat3).transpose * codeMat 143 * (codeMat 172 : Mat3).transpose = codeMat 140
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 238 ∈ o215W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 132, 96, 10, 1] 238 (by decide)
    have hact : actionA (codeMat 226) (codeMat 99) (codeMat 238) = codeMat 78 := by
      unfold actionA
      rw [step109wc334s29_QtInv]
      show (codeMat 226 : Mat3).transpose * codeMat 238 * (codeMat 172 : Mat3).transpose = codeMat 78
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 133 ∈ o215W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 132, 96, 10, 1] 133 (by decide)
    have hact : actionA (codeMat 226) (codeMat 99) (codeMat 133) = codeMat 44 := by
      unfold actionA
      rw [step109wc334s29_QtInv]
      show (codeMat 226 : Mat3).transpose * codeMat 133 * (codeMat 172 : Mat3).transpose = codeMat 44
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o215W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 132, 96, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 226) (codeMat 99) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step109wc334s29_QtInv]
      show (codeMat 226 : Mat3).transpose * codeMat 1 * (codeMat 172 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 325 ∈ o215W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 132, 96, 10, 1] 325 (by decide)
    have hact : actionA (codeMat 226) (codeMat 99) (codeMat 325) = codeMat 1 := by
      unfold actionA
      rw [step109wc334s29_QtInv]
      show (codeMat 226 : Mat3).transpose * codeMat 325 * (codeMat 172 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact

theorem step109wc334s29Dispatch :
    QuotientRankAtLeast (o334SourceU_wc ⟨29, by omega⟩) 14 := by
  have hP : Invertible (codeMat 226 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 99 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 226) (codeMat 99) o215W_mono) 14 :=
    @quotientRankAtLeast_action (codeMat 226) (codeMat 99) hP hQ o215W_mono 14
      orbit215_lb14_mono
  exact quotientRankAtLeast_mono step109wc334s29_contain hAct


private theorem step109wc334s30_QtInv :
    (codeMat 103 : Mat3).transpose⁻¹ = (codeMat 188 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 103 : Mat3).transpose * (codeMat 188 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc334s30_contain :
    (o334SourceU_wc ⟨30, by omega⟩) ≤ actionW (codeMat 234) (codeMat 103) o215W_mono := by
  change spanCodes [140, 76, 46, 16, 1] ≤ actionW (codeMat 234) (codeMat 103) o215W_mono
  apply step109wc334_spanCodes_le_of_gens [140, 76, 46, 16, 1]
    (actionW (codeMat 234) (codeMat 103) o215W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 143 ∈ o215W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 132, 96, 10, 1] 143 (by decide)
    have hact : actionA (codeMat 234) (codeMat 103) (codeMat 143) = codeMat 140 := by
      unfold actionA
      rw [step109wc334s30_QtInv]
      show (codeMat 234 : Mat3).transpose * codeMat 143 * (codeMat 188 : Mat3).transpose = codeMat 140
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 427 ∈ o215W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 132, 96, 10, 1] 427 (by decide)
    have hact : actionA (codeMat 234) (codeMat 103) (codeMat 427) = codeMat 76 := by
      unfold actionA
      rw [step109wc334s30_QtInv]
      show (codeMat 234 : Mat3).transpose * codeMat 427 * (codeMat 188 : Mat3).transpose = codeMat 76
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 132 ∈ o215W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 132, 96, 10, 1] 132 (by decide)
    have hact : actionA (codeMat 234) (codeMat 103) (codeMat 132) = codeMat 46 := by
      unfold actionA
      rw [step109wc334s30_QtInv]
      show (codeMat 234 : Mat3).transpose * codeMat 132 * (codeMat 188 : Mat3).transpose = codeMat 46
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o215W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 132, 96, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 234) (codeMat 103) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step109wc334s30_QtInv]
      show (codeMat 234 : Mat3).transpose * codeMat 1 * (codeMat 188 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 325 ∈ o215W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 132, 96, 10, 1] 325 (by decide)
    have hact : actionA (codeMat 234) (codeMat 103) (codeMat 325) = codeMat 1 := by
      unfold actionA
      rw [step109wc334s30_QtInv]
      show (codeMat 234 : Mat3).transpose * codeMat 325 * (codeMat 188 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc334_codeMat_mem_actionW_of_witness hw hact

theorem step109wc334s30Dispatch :
    QuotientRankAtLeast (o334SourceU_wc ⟨30, by omega⟩) 14 := by
  have hP : Invertible (codeMat 234 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 103 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 234) (codeMat 103) o215W_mono) 14 :=
    @quotientRankAtLeast_action (codeMat 234) (codeMat 103) hP hQ o215W_mono 14
      orbit215_lb14_mono
  exact quotientRankAtLeast_mono step109wc334s30_contain hAct

theorem step109wc334_all_dispatch (i : Fin 31) :
    QuotientRankAtLeast (o334SourceU_wc i) (o334SourceLb_wc i) := by
  fin_cases i
  · exact step109wc334s0Dispatch
  · exact step109wc334s1Dispatch
  · exact step109wc334s2Dispatch
  · exact step109wc334s3Dispatch
  · exact step109wc334s4Dispatch
  · exact step109wc334s5Dispatch
  · exact step109wc334s6Dispatch
  · exact step109wc334s7Dispatch
  · exact step109wc334s8Dispatch
  · exact step109wc334s9Dispatch
  · exact step109wc334s10Dispatch
  · exact step109wc334s11Dispatch
  · exact step109wc334s12Dispatch
  · exact step109wc334s13Dispatch
  · exact step109wc334s14Dispatch
  · exact step109wc334s15Dispatch
  · exact step109wc334s16Dispatch
  · exact step109wc334s17Dispatch
  · exact step109wc334s18Dispatch
  · exact step109wc334s19Dispatch
  · exact step109wc334s20Dispatch
  · exact step109wc334s21Dispatch
  · exact step109wc334s22Dispatch
  · exact step109wc334s23Dispatch
  · exact step109wc334s24Dispatch
  · exact step109wc334s25Dispatch
  · exact step109wc334s26Dispatch
  · exact step109wc334s27Dispatch
  · exact step109wc334s28Dispatch
  · exact step109wc334s29Dispatch
  · exact step109wc334s30Dispatch

theorem step109_orbit334_lb16_wc : QuotientRankAtLeast o334W_wc 16 :=
  o334Lb16_wc step109wc334_all_dispatch

end QiushiMatmul
