import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiWcOrbit113Consumer
import QiushiWcOrbit36Dispatch
import QiushiWcOrbit50Dispatch
import QiushiOrbit40FP
import QiushiMonoOrbit43From14
import QiushiOrbit10FP
import QiushiOrbit14FP
import QiushiWcOrbit25Dispatch
import QiushiFlattenSeeds

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc113_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc113_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc113s0_QtInv :
    (codeMat 305 : Mat3).transpose⁻¹ = (codeMat 305 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 305 : Mat3).transpose * (codeMat 305 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc113s0_contain :
    (o113SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 281) (codeMat 305) o36W_wc := by
  change spanCodes [384, 96, 20, 8, 2, 1] ≤ actionW (codeMat 281) (codeMat 305) o36W_wc
  apply step109wc113_spanCodes_le_of_gens [384, 96, 20, 8, 2, 1]
    (actionW (codeMat 281) (codeMat 305) o36W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 256 ∈ o36W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 281) (codeMat 305) (codeMat 256) = codeMat 384 := by
      unfold actionA
      rw [step109wc113s0_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 256 * (codeMat 305 : Mat3).transpose = codeMat 384
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 118 ∈ o36W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 20, 8, 2, 1] 118 (by decide)
    have hact : actionA (codeMat 281) (codeMat 305) (codeMat 118) = codeMat 96 := by
      unfold actionA
      rw [step109wc113s0_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 118 * (codeMat 305 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 20 ∈ o36W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 20, 8, 2, 1] 20 (by decide)
    have hact : actionA (codeMat 281) (codeMat 305) (codeMat 20) = codeMat 20 := by
      unfold actionA
      rw [step109wc113s0_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 20 * (codeMat 305 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 9 ∈ o36W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 20, 8, 2, 1] 9 (by decide)
    have hact : actionA (codeMat 281) (codeMat 305) (codeMat 9) = codeMat 8 := by
      unfold actionA
      rw [step109wc113s0_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 9 * (codeMat 305 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o36W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 281) (codeMat 305) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc113s0_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 2 * (codeMat 305 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o36W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 281) (codeMat 305) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc113s0_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 1 * (codeMat 305 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact

theorem step109wc113s0Dispatch :
    QuotientRankAtLeast (o113SourceU_wc ⟨0, by omega⟩) 13 := by
  have hP : Invertible (codeMat 281 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 281) (codeMat 305) o36W_wc) 13 :=
    @quotientRankAtLeast_action (codeMat 281) (codeMat 305) hP hQ o36W_wc 13
      step109_orbit36_lb13_wc
  exact quotientRankAtLeast_mono step109wc113s0_contain hAct


private theorem step109wc113s1_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = (codeMat 275 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * (codeMat 275 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc113s1_contain :
    (o113SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 465) (codeMat 275) o50W_wc := by
  change spanCodes [308, 180, 96, 8, 2, 1] ≤ actionW (codeMat 465) (codeMat 275) o50W_wc
  apply step109wc113_spanCodes_le_of_gens [308, 180, 96, 8, 2, 1]
    (actionW (codeMat 465) (codeMat 275) o50W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 280 ∈ o50W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 8, 2, 1] 280 (by decide)
    have hact : actionA (codeMat 465) (codeMat 275) (codeMat 280) = codeMat 308 := by
      unfold actionA
      rw [step109wc113s1_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 280 * (codeMat 275 : Mat3).transpose = codeMat 308
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 231 ∈ o50W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 8, 2, 1] 231 (by decide)
    have hact : actionA (codeMat 465) (codeMat 275) (codeMat 231) = codeMat 180 := by
      unfold actionA
      rw [step109wc113s1_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 231 * (codeMat 275 : Mat3).transpose = codeMat 180
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 105 ∈ o50W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 8, 2, 1] 105 (by decide)
    have hact : actionA (codeMat 465) (codeMat 275) (codeMat 105) = codeMat 96 := by
      unfold actionA
      rw [step109wc113s1_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 105 * (codeMat 275 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ o50W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 465) (codeMat 275) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step109wc113s1_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 8 * (codeMat 275 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ o50W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 8, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 465) (codeMat 275) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [step109wc113s1_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 3 * (codeMat 275 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o50W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 465) (codeMat 275) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc113s1_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 1 * (codeMat 275 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact

theorem step109wc113s1Dispatch :
    QuotientRankAtLeast (o113SourceU_wc ⟨1, by omega⟩) 13 := by
  have hP : Invertible (codeMat 465 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 465) (codeMat 275) o50W_wc) 13 :=
    @quotientRankAtLeast_action (codeMat 465) (codeMat 275) hP hQ o50W_wc 13
      step109_orbit50_lb13_wc
  exact quotientRankAtLeast_mono step109wc113s1_contain hAct


private theorem step109wc113s2_QtInv :
    (codeMat 417 : Mat3).transpose⁻¹ = (codeMat 177 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 417 : Mat3).transpose * (codeMat 177 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc113s2_contain :
    (o113SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 267) (codeMat 417) orbit40W := by
  change spanCodes [384, 84, 52, 8, 2, 1] ≤ actionW (codeMat 267) (codeMat 417) orbit40W
  apply step109wc113_spanCodes_le_of_gens [384, 84, 52, 8, 2, 1]
    (actionW (codeMat 267) (codeMat 417) orbit40W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 128 ∈ orbit40W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 128] 128 (by decide)
    have hact : actionA (codeMat 267) (codeMat 417) (codeMat 128) = codeMat 384 := by
      unfold actionA
      rw [step109wc113s2_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 128 * (codeMat 177 : Mat3).transpose = codeMat 384
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 84 ∈ orbit40W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 128] 84 (by decide)
    have hact : actionA (codeMat 267) (codeMat 417) (codeMat 84) = codeMat 84 := by
      unfold actionA
      rw [step109wc113s2_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 84 * (codeMat 177 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 34 ∈ orbit40W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 128] 34 (by decide)
    have hact : actionA (codeMat 267) (codeMat 417) (codeMat 34) = codeMat 52 := by
      unfold actionA
      rw [step109wc113s2_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 34 * (codeMat 177 : Mat3).transpose = codeMat 52
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 9 ∈ orbit40W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 128] 9 (by decide)
    have hact : actionA (codeMat 267) (codeMat 417) (codeMat 9) = codeMat 8 := by
      unfold actionA
      rw [step109wc113s2_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 9 * (codeMat 177 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 32 ∈ orbit40W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 128] 32 (by decide)
    have hact : actionA (codeMat 267) (codeMat 417) (codeMat 32) = codeMat 2 := by
      unfold actionA
      rw [step109wc113s2_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 32 * (codeMat 177 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ orbit40W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 128] 8 (by decide)
    have hact : actionA (codeMat 267) (codeMat 417) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc113s2_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 8 * (codeMat 177 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact

theorem step109wc113s2Dispatch :
    QuotientRankAtLeast (o113SourceU_wc ⟨2, by omega⟩) 12 := by
  have hP : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 267) (codeMat 417) orbit40W) 12 :=
    @quotientRankAtLeast_action (codeMat 267) (codeMat 417) hP hQ orbit40W 12
      orbit40_lb12
  exact quotientRankAtLeast_mono step109wc113s2_contain hAct


private theorem step109wc113s3_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc113s3_contain :
    (o113SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 161) (codeMat 266) o43W_mono := by
  change spanCodes [256, 128, 96, 8, 2, 1] ≤ actionW (codeMat 161) (codeMat 266) o43W_mono
  apply step109wc113_spanCodes_le_of_gens [256, 128, 96, 8, 2, 1]
    (actionW (codeMat 161) (codeMat 266) o43W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 32 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 32) = codeMat 256 := by
      unfold actionA
      rw [step109wc113s3_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 32 * (codeMat 266 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 8 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 8) = codeMat 128 := by
      unfold actionA
      rw [step109wc113s3_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 8 * (codeMat 266 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 272 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 272 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 272) = codeMat 96 := by
      unfold actionA
      rw [step109wc113s3_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 272 * (codeMat 266 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 128 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 128) = codeMat 8 := by
      unfold actionA
      rw [step109wc113s3_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 128 * (codeMat 266 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 1) = codeMat 2 := by
      unfold actionA
      rw [step109wc113s3_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc113s3_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact

theorem step109wc113s3Dispatch :
    QuotientRankAtLeast (o113SourceU_wc ⟨3, by omega⟩) 12 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 266) o43W_mono) 12 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 266) hP hQ o43W_mono 12
      orbit43_lb12_mono
  exact quotientRankAtLeast_mono step109wc113s3_contain hAct


private theorem step109wc113s4_QtInv :
    (codeMat 305 : Mat3).transpose⁻¹ = (codeMat 305 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 305 : Mat3).transpose * (codeMat 305 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc113s4_contain :
    (o113SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 266) (codeMat 305) orbit10W := by
  change spanCodes [260, 132, 96, 16, 8, 2, 1] ≤ actionW (codeMat 266) (codeMat 305) orbit10W
  apply step109wc113_spanCodes_le_of_gens [260, 132, 96, 16, 8, 2, 1]
    (actionW (codeMat 266) (codeMat 305) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 432 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 432 (by decide)
    have hact : actionA (codeMat 266) (codeMat 305) (codeMat 432) = codeMat 260 := by
      unfold actionA
      rw [step109wc113s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 432 * (codeMat 305 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 176 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 176 (by decide)
    have hact : actionA (codeMat 266) (codeMat 305) (codeMat 176) = codeMat 132 := by
      unfold actionA
      rw [step109wc113s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 176 * (codeMat 305 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 70 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 70 (by decide)
    have hact : actionA (codeMat 266) (codeMat 305) (codeMat 70) = codeMat 96 := by
      unfold actionA
      rw [step109wc113s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 70 * (codeMat 305 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 305) (codeMat 2) = codeMat 16 := by
      unfold actionA
      rw [step109wc113s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 305 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 305) (codeMat 1) = codeMat 8 := by
      unfold actionA
      rw [step109wc113s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 305 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 305) (codeMat 16) = codeMat 2 := by
      unfold actionA
      rw [step109wc113s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 305 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 305) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc113s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 305 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact

theorem step109wc113s4Dispatch :
    QuotientRankAtLeast (o113SourceU_wc ⟨4, by omega⟩) 12 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 305) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 305) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc113s4_contain hAct


private theorem step109wc113s5_QtInv :
    (codeMat 314 : Mat3).transpose⁻¹ = (codeMat 271 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 314 : Mat3).transpose * (codeMat 271 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc113s5_contain :
    (o113SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 161) (codeMat 314) o43W_mono := by
  change spanCodes [288, 160, 96, 8, 2, 1] ≤ actionW (codeMat 161) (codeMat 314) o43W_mono
  apply step109wc113_spanCodes_le_of_gens [288, 160, 96, 8, 2, 1]
    (actionW (codeMat 161) (codeMat 314) o43W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 432 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 432 (by decide)
    have hact : actionA (codeMat 161) (codeMat 314) (codeMat 432) = codeMat 288 := by
      unfold actionA
      rw [step109wc113s5_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 432 * (codeMat 271 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 408 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 408 (by decide)
    have hact : actionA (codeMat 161) (codeMat 314) (codeMat 408) = codeMat 160 := by
      unfold actionA
      rw [step109wc113s5_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 408 * (codeMat 271 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 400 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 400 (by decide)
    have hact : actionA (codeMat 161) (codeMat 314) (codeMat 400) = codeMat 96 := by
      unfold actionA
      rw [step109wc113s5_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 400 * (codeMat 271 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 128 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 161) (codeMat 314) (codeMat 128) = codeMat 8 := by
      unfold actionA
      rw [step109wc113s5_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 128 * (codeMat 271 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 161) (codeMat 314) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [step109wc113s5_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 3 * (codeMat 271 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 314) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc113s5_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 271 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact

theorem step109wc113s5Dispatch :
    QuotientRankAtLeast (o113SourceU_wc ⟨5, by omega⟩) 12 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 314 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 314) o43W_mono) 12 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 314) hP hQ o43W_mono 12
      orbit43_lb12_mono
  exact quotientRankAtLeast_mono step109wc113s5_contain hAct


private theorem step109wc113s6_QtInv :
    (codeMat 444 : Mat3).transpose⁻¹ = (codeMat 110 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 444 : Mat3).transpose * (codeMat 110 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc113s6_contain :
    (o113SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 98) (codeMat 444) orbit14W := by
  change spanCodes [276, 148, 80, 48, 8, 2, 1] ≤ actionW (codeMat 98) (codeMat 444) orbit14W
  apply step109wc113_spanCodes_le_of_gens [276, 148, 80, 48, 8, 2, 1]
    (actionW (codeMat 98) (codeMat 444) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 510 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 510 (by decide)
    have hact : actionA (codeMat 98) (codeMat 444) (codeMat 510) = codeMat 276 := by
      unfold actionA
      rw [step109wc113s6_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 510 * (codeMat 110 : Mat3).transpose = codeMat 276
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 502 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 502 (by decide)
    have hact : actionA (codeMat 98) (codeMat 444) (codeMat 502) = codeMat 148 := by
      unfold actionA
      rw [step109wc113s6_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 502 * (codeMat 110 : Mat3).transpose = codeMat 148
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 22 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 22 (by decide)
    have hact : actionA (codeMat 98) (codeMat 444) (codeMat 22) = codeMat 80 := by
      unfold actionA
      rw [step109wc113s6_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 22 * (codeMat 110 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 98) (codeMat 444) (codeMat 1) = codeMat 48 := by
      unfold actionA
      rw [step109wc113s6_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 1 * (codeMat 110 : Mat3).transpose = codeMat 48
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 98) (codeMat 444) (codeMat 2) = codeMat 8 := by
      unfold actionA
      rw [step109wc113s6_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 2 * (codeMat 110 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 98) (codeMat 444) (codeMat 384) = codeMat 2 := by
      unfold actionA
      rw [step109wc113s6_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 384 * (codeMat 110 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 98) (codeMat 444) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc113s6_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 128 * (codeMat 110 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact

theorem step109wc113s6Dispatch :
    QuotientRankAtLeast (o113SourceU_wc ⟨6, by omega⟩) 12 := by
  have hP : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 444 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 98) (codeMat 444) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 98) (codeMat 444) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc113s6_contain hAct


private theorem step109wc113s7_QtInv :
    (codeMat 282 : Mat3).transpose⁻¹ = (codeMat 267 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 282 : Mat3).transpose * (codeMat 267 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc113s7_contain :
    (o113SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 241) (codeMat 282) orbit14W := by
  change spanCodes [276, 148, 68, 36, 8, 2, 1] ≤ actionW (codeMat 241) (codeMat 282) orbit14W
  apply step109wc113_spanCodes_le_of_gens [276, 148, 68, 36, 8, 2, 1]
    (actionW (codeMat 241) (codeMat 282) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 483 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 483 (by decide)
    have hact : actionA (codeMat 241) (codeMat 282) (codeMat 483) = codeMat 276 := by
      unfold actionA
      rw [step109wc113s7_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 483 * (codeMat 267 : Mat3).transpose = codeMat 276
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 28 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 28 (by decide)
    have hact : actionA (codeMat 241) (codeMat 282) (codeMat 28) = codeMat 148 := by
      unfold actionA
      rw [step109wc113s7_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 28 * (codeMat 267 : Mat3).transpose = codeMat 148
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 150 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 150 (by decide)
    have hact : actionA (codeMat 241) (codeMat 282) (codeMat 150) = codeMat 68 := by
      unfold actionA
      rw [step109wc113s7_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 150 * (codeMat 267 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 241) (codeMat 282) (codeMat 256) = codeMat 36 := by
      unfold actionA
      rw [step109wc113s7_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 256 * (codeMat 267 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 130 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 130 (by decide)
    have hact : actionA (codeMat 241) (codeMat 282) (codeMat 130) = codeMat 8 := by
      unfold actionA
      rw [step109wc113s7_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 130 * (codeMat 267 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 241) (codeMat 282) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [step109wc113s7_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 3 * (codeMat 267 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 241) (codeMat 282) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc113s7_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 2 * (codeMat 267 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact

theorem step109wc113s7Dispatch :
    QuotientRankAtLeast (o113SourceU_wc ⟨7, by omega⟩) 12 := by
  have hP : Invertible (codeMat 241 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 282 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 241) (codeMat 282) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 241) (codeMat 282) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc113s7_contain hAct


private theorem step109wc113s8_QtInv :
    (codeMat 298 : Mat3).transpose⁻¹ = (codeMat 270 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 298 : Mat3).transpose * (codeMat 270 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc113s8_contain :
    (o113SourceU_wc ⟨8, by omega⟩) ≤ actionW (codeMat 241) (codeMat 298) orbit14W := by
  change spanCodes [272, 144, 68, 36, 8, 2, 1] ≤ actionW (codeMat 241) (codeMat 298) orbit14W
  apply step109wc113_spanCodes_le_of_gens [272, 144, 68, 36, 8, 2, 1]
    (actionW (codeMat 241) (codeMat 298) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 503 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 503 (by decide)
    have hact : actionA (codeMat 241) (codeMat 298) (codeMat 503) = codeMat 272 := by
      unfold actionA
      rw [step109wc113s8_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 503 * (codeMat 270 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 241) (codeMat 298) (codeMat 8) = codeMat 144 := by
      unfold actionA
      rw [step109wc113s8_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 8 * (codeMat 270 : Mat3).transpose = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 148 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 148 (by decide)
    have hact : actionA (codeMat 241) (codeMat 298) (codeMat 148) = codeMat 68 := by
      unfold actionA
      rw [step109wc113s8_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 148 * (codeMat 270 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 241) (codeMat 298) (codeMat 384) = codeMat 36 := by
      unfold actionA
      rw [step109wc113s8_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 384 * (codeMat 270 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 130 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 130 (by decide)
    have hact : actionA (codeMat 241) (codeMat 298) (codeMat 130) = codeMat 8 := by
      unfold actionA
      rw [step109wc113s8_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 130 * (codeMat 270 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 241) (codeMat 298) (codeMat 1) = codeMat 2 := by
      unfold actionA
      rw [step109wc113s8_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 1 * (codeMat 270 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 241) (codeMat 298) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc113s8_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 2 * (codeMat 270 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact

theorem step109wc113s8Dispatch :
    QuotientRankAtLeast (o113SourceU_wc ⟨8, by omega⟩) 12 := by
  have hP : Invertible (codeMat 241 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 298 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 241) (codeMat 298) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 241) (codeMat 298) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc113s8_contain hAct


private theorem step109wc113s9_QtInv :
    (codeMat 177 : Mat3).transpose⁻¹ = (codeMat 417 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 177 : Mat3).transpose * (codeMat 417 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc113s9_contain :
    (o113SourceU_wc ⟨9, by omega⟩) ≤ actionW (codeMat 273) (codeMat 177) o25W_wc := by
  change spanCodes [384, 96, 8, 4, 2, 1] ≤ actionW (codeMat 273) (codeMat 177) o25W_wc
  apply step109wc113_spanCodes_le_of_gens [384, 96, 8, 4, 2, 1]
    (actionW (codeMat 273) (codeMat 177) o25W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 256 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 273) (codeMat 177) (codeMat 256) = codeMat 384 := by
      unfold actionA
      rw [step109wc113s9_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 256 * (codeMat 417 : Mat3).transpose = codeMat 384
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 80 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 80 (by decide)
    have hact : actionA (codeMat 273) (codeMat 177) (codeMat 80) = codeMat 96 := by
      unfold actionA
      rw [step109wc113s9_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 80 * (codeMat 417 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 177) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step109wc113s9_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 417 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 177) (codeMat 2) = codeMat 4 := by
      unfold actionA
      rw [step109wc113s9_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 417 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 6 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 6 (by decide)
    have hact : actionA (codeMat 273) (codeMat 177) (codeMat 6) = codeMat 2 := by
      unfold actionA
      rw [step109wc113s9_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 6 * (codeMat 417 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 177) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc113s9_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 417 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact

theorem step109wc113s9Dispatch :
    QuotientRankAtLeast (o113SourceU_wc ⟨9, by omega⟩) 11 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 177) o25W_wc) 11 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 177) hP hQ o25W_wc 11
      step109_orbit25_lb11_wc
  exact quotientRankAtLeast_mono step109wc113s9_contain hAct

private def step109wc113s10SrcT : Submodule F2 Mat3 := spanCodes [256, 132, 64, 16, 8, 2, 1]

private theorem step109wc113s10SrcT_lb : QuotientRankAtLeast step109wc113s10SrcT 9 := by
  have ht := quotientRankAtLeast_transpose flatSeed_7
  have hle : step109wc113s10SrcT ≤ transposeW flatW_7 := by
    unfold step109wc113s10SrcT transposeW
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

private theorem step109wc113s10_QtInv :
    (codeMat 417 : Mat3).transpose⁻¹ = (codeMat 177 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 417 : Mat3).transpose * (codeMat 177 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc113s10_contain :
    (o113SourceU_wc ⟨10, by omega⟩) ≤ actionW (codeMat 99) (codeMat 417) step109wc113s10SrcT := by
  change spanCodes [384, 64, 32, 20, 8, 2, 1] ≤ actionW (codeMat 99) (codeMat 417) step109wc113s10SrcT
  apply step109wc113_spanCodes_le_of_gens [384, 64, 32, 20, 8, 2, 1]
    (actionW (codeMat 99) (codeMat 417) step109wc113s10SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 16 ∈ step109wc113s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 16, 8, 2, 1] 16 (by decide)
    have hact : actionA (codeMat 99) (codeMat 417) (codeMat 16) = codeMat 384 := by
      unfold actionA
      rw [step109wc113s10_QtInv]
      show (codeMat 99 : Mat3).transpose * codeMat 16 * (codeMat 177 : Mat3).transpose = codeMat 384
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 8 ∈ step109wc113s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 16, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 99) (codeMat 417) (codeMat 8) = codeMat 64 := by
      unfold actionA
      rw [step109wc113s10_QtInv]
      show (codeMat 99 : Mat3).transpose * codeMat 8 * (codeMat 177 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 390 ∈ step109wc113s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 16, 8, 2, 1] 390 (by decide)
    have hact : actionA (codeMat 99) (codeMat 417) (codeMat 390) = codeMat 32 := by
      unfold actionA
      rw [step109wc113s10_QtInv]
      show (codeMat 99 : Mat3).transpose * codeMat 390 * (codeMat 177 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 132 ∈ step109wc113s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 16, 8, 2, 1] 132 (by decide)
    have hact : actionA (codeMat 99) (codeMat 417) (codeMat 132) = codeMat 20 := by
      unfold actionA
      rw [step109wc113s10_QtInv]
      show (codeMat 99 : Mat3).transpose * codeMat 132 * (codeMat 177 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 65 ∈ step109wc113s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 16, 8, 2, 1] 65 (by decide)
    have hact : actionA (codeMat 99) (codeMat 417) (codeMat 65) = codeMat 8 := by
      unfold actionA
      rw [step109wc113s10_QtInv]
      show (codeMat 99 : Mat3).transpose * codeMat 65 * (codeMat 177 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 256 ∈ step109wc113s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 16, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 99) (codeMat 417) (codeMat 256) = codeMat 2 := by
      unfold actionA
      rw [step109wc113s10_QtInv]
      show (codeMat 99 : Mat3).transpose * codeMat 256 * (codeMat 177 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 64 ∈ step109wc113s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 16, 8, 2, 1] 64 (by decide)
    have hact : actionA (codeMat 99) (codeMat 417) (codeMat 64) = codeMat 1 := by
      unfold actionA
      rw [step109wc113s10_QtInv]
      show (codeMat 99 : Mat3).transpose * codeMat 64 * (codeMat 177 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact

theorem step109wc113s10Dispatch :
    QuotientRankAtLeast (o113SourceU_wc ⟨10, by omega⟩) 9 := by
  have hP : Invertible (codeMat 99 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 99) (codeMat 417) step109wc113s10SrcT) 9 :=
    @quotientRankAtLeast_action (codeMat 99) (codeMat 417) hP hQ step109wc113s10SrcT 9
      step109wc113s10SrcT_lb
  exact quotientRankAtLeast_mono step109wc113s10_contain hAct

private def step109wc113s11SrcT : Submodule F2 Mat3 := spanCodes [256, 132, 64, 16, 8, 2, 1]

private theorem step109wc113s11SrcT_lb : QuotientRankAtLeast step109wc113s11SrcT 9 := by
  have ht := quotientRankAtLeast_transpose flatSeed_7
  have hle : step109wc113s11SrcT ≤ transposeW flatW_7 := by
    unfold step109wc113s11SrcT transposeW
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

private theorem step109wc113s11_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc113s11_contain :
    (o113SourceU_wc ⟨11, by omega⟩) ≤ actionW (codeMat 142) (codeMat 273) step109wc113s11SrcT := by
  change spanCodes [272, 144, 64, 32, 8, 2, 1] ≤ actionW (codeMat 142) (codeMat 273) step109wc113s11SrcT
  apply step109wc113_spanCodes_le_of_gens [272, 144, 64, 32, 8, 2, 1]
    (actionW (codeMat 142) (codeMat 273) step109wc113s11SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 388 ∈ step109wc113s11SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 16, 8, 2, 1] 388 (by decide)
    have hact : actionA (codeMat 142) (codeMat 273) (codeMat 388) = codeMat 272 := by
      unfold actionA
      rw [step109wc113s11_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 388 * (codeMat 273 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ step109wc113s11SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 16, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 142) (codeMat 273) (codeMat 2) = codeMat 144 := by
      unfold actionA
      rw [step109wc113s11_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 65 ∈ step109wc113s11SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 16, 8, 2, 1] 65 (by decide)
    have hact : actionA (codeMat 142) (codeMat 273) (codeMat 65) = codeMat 64 := by
      unfold actionA
      rw [step109wc113s11_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 65 * (codeMat 273 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ step109wc113s11SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 16, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 142) (codeMat 273) (codeMat 256) = codeMat 32 := by
      unfold actionA
      rw [step109wc113s11_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 256 * (codeMat 273 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 64 ∈ step109wc113s11SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 16, 8, 2, 1] 64 (by decide)
    have hact : actionA (codeMat 142) (codeMat 273) (codeMat 64) = codeMat 8 := by
      unfold actionA
      rw [step109wc113s11_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 64 * (codeMat 273 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ step109wc113s11SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 16, 8, 2, 1] 16 (by decide)
    have hact : actionA (codeMat 142) (codeMat 273) (codeMat 16) = codeMat 2 := by
      unfold actionA
      rw [step109wc113s11_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 16 * (codeMat 273 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ step109wc113s11SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 16, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 142) (codeMat 273) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc113s11_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 8 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc113_codeMat_mem_actionW_of_witness hw hact

theorem step109wc113s11Dispatch :
    QuotientRankAtLeast (o113SourceU_wc ⟨11, by omega⟩) 9 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 273) step109wc113s11SrcT) 9 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 273) hP hQ step109wc113s11SrcT 9
      step109wc113s11SrcT_lb
  exact quotientRankAtLeast_mono step109wc113s11_contain hAct

theorem step109wc113_all_dispatch (i : Fin 12) :
    QuotientRankAtLeast (o113SourceU_wc i) (o113SourceLb_wc i) := by
  fin_cases i
  · exact step109wc113s0Dispatch
  · exact step109wc113s1Dispatch
  · exact step109wc113s2Dispatch
  · exact step109wc113s3Dispatch
  · exact step109wc113s4Dispatch
  · exact step109wc113s5Dispatch
  · exact step109wc113s6Dispatch
  · exact step109wc113s7Dispatch
  · exact step109wc113s8Dispatch
  · exact step109wc113s9Dispatch
  · exact step109wc113s10Dispatch
  · exact step109wc113s11Dispatch

theorem step109_orbit113_lb14_wc : QuotientRankAtLeast o113W_wc 14 :=
  o113Lb14_wc step109wc113_all_dispatch

end QiushiMatmul
