import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiWcOrbit114Consumer
import QiushiWcOrbit50Dispatch
import QiushiMonoOrbit43From14
import QiushiOrbit10FP
import QiushiWcOrbit25Dispatch
import QiushiFlattenSeeds

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc114_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc114_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc114s0_QtInv :
    (codeMat 311 : Mat3).transpose⁻¹ = (codeMat 307 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 311 : Mat3).transpose * (codeMat 307 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc114s0_contain :
    (o114SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 409) (codeMat 311) o50W_wc := by
  change spanCodes [256, 160, 116, 8, 2, 1] ≤ actionW (codeMat 409) (codeMat 311) o50W_wc
  apply step109wc114_spanCodes_le_of_gens [256, 160, 116, 8, 2, 1]
    (actionW (codeMat 409) (codeMat 311) o50W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 511 ∈ o50W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 8, 2, 1] 511 (by decide)
    have hact : actionA (codeMat 409) (codeMat 311) (codeMat 511) = codeMat 256 := by
      unfold actionA
      rw [step109wc114s0_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 511 * (codeMat 307 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 228 ∈ o50W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 8, 2, 1] 228 (by decide)
    have hact : actionA (codeMat 409) (codeMat 311) (codeMat 228) = codeMat 160 := by
      unfold actionA
      rw [step109wc114s0_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 228 * (codeMat 307 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 106 ∈ o50W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 8, 2, 1] 106 (by decide)
    have hact : actionA (codeMat 409) (codeMat 311) (codeMat 106) = codeMat 116 := by
      unfold actionA
      rw [step109wc114s0_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 106 * (codeMat 307 : Mat3).transpose = codeMat 116
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 9 ∈ o50W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 8, 2, 1] 9 (by decide)
    have hact : actionA (codeMat 409) (codeMat 311) (codeMat 9) = codeMat 8 := by
      unfold actionA
      rw [step109wc114s0_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 9 * (codeMat 307 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ o50W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 8, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 409) (codeMat 311) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [step109wc114s0_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 3 * (codeMat 307 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o50W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 409) (codeMat 311) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc114s0_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 1 * (codeMat 307 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact

theorem step109wc114s0Dispatch :
    QuotientRankAtLeast (o114SourceU_wc ⟨0, by omega⟩) 13 := by
  have hP : Invertible (codeMat 409 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 311 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 409) (codeMat 311) o50W_wc) 13 :=
    @quotientRankAtLeast_action (codeMat 409) (codeMat 311) hP hQ o50W_wc 13
      step109_orbit50_lb13_wc
  exact quotientRankAtLeast_mono step109wc114s0_contain hAct


private theorem step109wc114s1_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc114s1_contain :
    (o114SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 267) (codeMat 161) o43W_mono := by
  change spanCodes [256, 132, 36, 8, 2, 1] ≤ actionW (codeMat 267) (codeMat 161) o43W_mono
  apply step109wc114_spanCodes_le_of_gens [256, 132, 36, 8, 2, 1]
    (actionW (codeMat 267) (codeMat 161) o43W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 128 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 267) (codeMat 161) (codeMat 128) = codeMat 256 := by
      unfold actionA
      rw [step109wc114s1_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 128 * (codeMat 161 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 272 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 272 (by decide)
    have hact : actionA (codeMat 267) (codeMat 161) (codeMat 272) = codeMat 132 := by
      unfold actionA
      rw [step109wc114s1_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 272 * (codeMat 161 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 267) (codeMat 161) (codeMat 2) = codeMat 36 := by
      unfold actionA
      rw [step109wc114s1_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 2 * (codeMat 161 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 9 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 9 (by decide)
    have hact : actionA (codeMat 267) (codeMat 161) (codeMat 9) = codeMat 8 := by
      unfold actionA
      rw [step109wc114s1_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 9 * (codeMat 161 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 32 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 267) (codeMat 161) (codeMat 32) = codeMat 2 := by
      unfold actionA
      rw [step109wc114s1_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 32 * (codeMat 161 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 267) (codeMat 161) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc114s1_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 8 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact

theorem step109wc114s1Dispatch :
    QuotientRankAtLeast (o114SourceU_wc ⟨1, by omega⟩) 12 := by
  have hP : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 267) (codeMat 161) o43W_mono) 12 :=
    @quotientRankAtLeast_action (codeMat 267) (codeMat 161) hP hQ o43W_mono 12
      orbit43_lb12_mono
  exact quotientRankAtLeast_mono step109wc114s1_contain hAct


private theorem step109wc114s2_QtInv :
    (codeMat 305 : Mat3).transpose⁻¹ = (codeMat 305 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 305 : Mat3).transpose * (codeMat 305 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc114s2_contain :
    (o114SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 401) (codeMat 305) o43W_mono := by
  change spanCodes [256, 144, 48, 8, 2, 1] ≤ actionW (codeMat 401) (codeMat 305) o43W_mono
  apply step109wc114_spanCodes_le_of_gens [256, 144, 48, 8, 2, 1]
    (actionW (codeMat 401) (codeMat 305) o43W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 432 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 432 (by decide)
    have hact : actionA (codeMat 401) (codeMat 305) (codeMat 432) = codeMat 256 := by
      unfold actionA
      rw [step109wc114s2_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 432 * (codeMat 305 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 128 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 401) (codeMat 305) (codeMat 128) = codeMat 144 := by
      unfold actionA
      rw [step109wc114s2_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 128 * (codeMat 305 : Mat3).transpose = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 32 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 401) (codeMat 305) (codeMat 32) = codeMat 48 := by
      unfold actionA
      rw [step109wc114s2_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 32 * (codeMat 305 : Mat3).transpose = codeMat 48
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 401) (codeMat 305) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step109wc114s2_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 8 * (codeMat 305 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 401) (codeMat 305) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc114s2_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 2 * (codeMat 305 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 401) (codeMat 305) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc114s2_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 1 * (codeMat 305 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact

theorem step109wc114s2Dispatch :
    QuotientRankAtLeast (o114SourceU_wc ⟨2, by omega⟩) 12 := by
  have hP : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 401) (codeMat 305) o43W_mono) 12 :=
    @quotientRankAtLeast_action (codeMat 401) (codeMat 305) hP hQ o43W_mono 12
      orbit43_lb12_mono
  exact quotientRankAtLeast_mono step109wc114s2_contain hAct


private theorem step109wc114s3_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc114s3_contain :
    (o114SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 266) (codeMat 266) orbit10W := by
  change spanCodes [256, 160, 68, 16, 8, 2, 1] ≤ actionW (codeMat 266) (codeMat 266) orbit10W
  apply step109wc114_spanCodes_le_of_gens [256, 160, 68, 16, 8, 2, 1]
    (actionW (codeMat 266) (codeMat 266) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 256) = codeMat 256 := by
      unfold actionA
      rw [step109wc114s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 256 * (codeMat 266 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 68 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 68) = codeMat 160 := by
      unfold actionA
      rw [step109wc114s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 68 * (codeMat 266 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 160) = codeMat 68 := by
      unfold actionA
      rw [step109wc114s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 160 * (codeMat 266 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step109wc114s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 2) = codeMat 8 := by
      unfold actionA
      rw [step109wc114s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 266 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 8) = codeMat 2 := by
      unfold actionA
      rw [step109wc114s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 266 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc114s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact

theorem step109wc114s3Dispatch :
    QuotientRankAtLeast (o114SourceU_wc ⟨3, by omega⟩) 12 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 266) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 266) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc114s3_contain hAct


private theorem step109wc114s4_QtInv :
    (codeMat 282 : Mat3).transpose⁻¹ = (codeMat 267 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 282 : Mat3).transpose * (codeMat 267 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc114s4_contain :
    (o114SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 161) (codeMat 282) o43W_mono := by
  change spanCodes [256, 160, 96, 8, 2, 1] ≤ actionW (codeMat 161) (codeMat 282) o43W_mono
  apply step109wc114_spanCodes_le_of_gens [256, 160, 96, 8, 2, 1]
    (actionW (codeMat 161) (codeMat 282) o43W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 32 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 161) (codeMat 282) (codeMat 32) = codeMat 256 := by
      unfold actionA
      rw [step109wc114s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 32 * (codeMat 267 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 280 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 280 (by decide)
    have hact : actionA (codeMat 161) (codeMat 282) (codeMat 280) = codeMat 160 := by
      unfold actionA
      rw [step109wc114s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 280 * (codeMat 267 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 272 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 272 (by decide)
    have hact : actionA (codeMat 161) (codeMat 282) (codeMat 272) = codeMat 96 := by
      unfold actionA
      rw [step109wc114s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 272 * (codeMat 267 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 128 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 161) (codeMat 282) (codeMat 128) = codeMat 8 := by
      unfold actionA
      rw [step109wc114s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 128 * (codeMat 267 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 161) (codeMat 282) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [step109wc114s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 3 * (codeMat 267 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 282) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc114s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 267 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact

theorem step109wc114s4Dispatch :
    QuotientRankAtLeast (o114SourceU_wc ⟨4, by omega⟩) 12 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 282 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 282) o43W_mono) 12 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 282) hP hQ o43W_mono 12
      orbit43_lb12_mono
  exact quotientRankAtLeast_mono step109wc114s4_contain hAct


private theorem step109wc114s5_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc114s5_contain :
    (o114SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 161) (codeMat 84) o25W_wc := by
  change spanCodes [256, 160, 8, 4, 2, 1] ≤ actionW (codeMat 161) (codeMat 84) o25W_wc
  apply step109wc114_spanCodes_le_of_gens [256, 160, 8, 4, 2, 1]
    (actionW (codeMat 161) (codeMat 84) o25W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 8 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 161) (codeMat 84) (codeMat 8) = codeMat 256 := by
      unfold actionA
      rw [step109wc114s5_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 8 * (codeMat 84 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 80 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 80 (by decide)
    have hact : actionA (codeMat 161) (codeMat 84) (codeMat 80) = codeMat 160 := by
      unfold actionA
      rw [step109wc114s5_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 80 * (codeMat 84 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 256 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 161) (codeMat 84) (codeMat 256) = codeMat 8 := by
      unfold actionA
      rw [step109wc114s5_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 256 * (codeMat 84 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 84) (codeMat 1) = codeMat 4 := by
      unfold actionA
      rw [step109wc114s5_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 84 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 84) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc114s5_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 84 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 4 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 4 (by decide)
    have hact : actionA (codeMat 161) (codeMat 84) (codeMat 4) = codeMat 1 := by
      unfold actionA
      rw [step109wc114s5_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 4 * (codeMat 84 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact

theorem step109wc114s5Dispatch :
    QuotientRankAtLeast (o114SourceU_wc ⟨5, by omega⟩) 11 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 84) o25W_wc) 11 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 84) hP hQ o25W_wc 11
      step109_orbit25_lb11_wc
  exact quotientRankAtLeast_mono step109wc114s5_contain hAct

private def step109wc114s6SrcT : Submodule F2 Mat3 := spanCodes [256, 64, 20, 8, 2, 1]

private theorem step109wc114s6SrcT_lb : QuotientRankAtLeast step109wc114s6SrcT 11 := by
  have ht := quotientRankAtLeast_transpose step109_orbit25_lb11_wc
  have hle : step109wc114s6SrcT ≤ transposeW o25W_wc := by
    unfold step109wc114s6SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4 | h5
    · subst h0
      show codeMat 256 ∈ Submodule.map transposeLinearMap o25W_wc
      exact ⟨codeMat 256, spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 256 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 64 ∈ Submodule.map transposeLinearMap o25W_wc
      exact ⟨codeMat 4, spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 4 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 20 ∈ Submodule.map transposeLinearMap o25W_wc
      exact ⟨codeMat 80, spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 80 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 8 ∈ Submodule.map transposeLinearMap o25W_wc
      exact ⟨codeMat 2, spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 2 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 2 ∈ Submodule.map transposeLinearMap o25W_wc
      exact ⟨codeMat 8, spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 8 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h5
      show codeMat 1 ∈ Submodule.map transposeLinearMap o25W_wc
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc114s6_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc114s6_contain :
    (o114SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 84) (codeMat 161) step109wc114s6SrcT := by
  change spanCodes [256, 160, 64, 8, 2, 1] ≤ actionW (codeMat 84) (codeMat 161) step109wc114s6SrcT
  apply step109wc114_spanCodes_le_of_gens [256, 160, 64, 8, 2, 1]
    (actionW (codeMat 84) (codeMat 161) step109wc114s6SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 2 ∈ step109wc114s6SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 64, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 161) (codeMat 2) = codeMat 256 := by
      unfold actionA
      rw [step109wc114s6_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 161 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 20 ∈ step109wc114s6SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 64, 20, 8, 2, 1] 20 (by decide)
    have hact : actionA (codeMat 84) (codeMat 161) (codeMat 20) = codeMat 160 := by
      unfold actionA
      rw [step109wc114s6_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 20 * (codeMat 161 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ step109wc114s6SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 64, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 161) (codeMat 1) = codeMat 64 := by
      unfold actionA
      rw [step109wc114s6_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ step109wc114s6SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 64, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 161) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step109wc114s6_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 161 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 256 ∈ step109wc114s6SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 64, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 161) (codeMat 256) = codeMat 2 := by
      unfold actionA
      rw [step109wc114s6_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 161 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 64 ∈ step109wc114s6SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 64, 20, 8, 2, 1] 64 (by decide)
    have hact : actionA (codeMat 84) (codeMat 161) (codeMat 64) = codeMat 1 := by
      unfold actionA
      rw [step109wc114s6_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 64 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact

theorem step109wc114s6Dispatch :
    QuotientRankAtLeast (o114SourceU_wc ⟨6, by omega⟩) 11 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 161) step109wc114s6SrcT) 11 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 161) hP hQ step109wc114s6SrcT 11
      step109wc114s6SrcT_lb
  exact quotientRankAtLeast_mono step109wc114s6_contain hAct


private theorem step109wc114s7_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc114s7_contain :
    (o114SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 84) (codeMat 84) flatW_3 := by
  change spanCodes [256, 128, 68, 32, 20, 8, 2, 1] ≤ actionW (codeMat 84) (codeMat 84) flatW_3
  apply step109wc114_spanCodes_le_of_gens [256, 128, 68, 32, 20, 8, 2, 1]
    (actionW (codeMat 84) (codeMat 84) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 1 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step109wc114s7_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 84 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 2) = codeMat 128 := by
      unfold actionA
      rw [step109wc114s7_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 84 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 68 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 68) = codeMat 68 := by
      unfold actionA
      rw [step109wc114s7_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 68 * (codeMat 84 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc114s7_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 84 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 80 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 80 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 80) = codeMat 20 := by
      unfold actionA
      rw [step109wc114s7_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 80 * (codeMat 84 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 32) = codeMat 8 := by
      unfold actionA
      rw [step109wc114s7_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 32 * (codeMat 84 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 128) = codeMat 2 := by
      unfold actionA
      rw [step109wc114s7_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 84 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 256 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc114s7_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 84 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc114_codeMat_mem_actionW_of_witness hw hact

theorem step109wc114s7Dispatch :
    QuotientRankAtLeast (o114SourceU_wc ⟨7, by omega⟩) 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 84) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 84) hP hQ flatW_3 9
      flatSeed_3
  exact quotientRankAtLeast_mono step109wc114s7_contain hAct

theorem step109wc114_all_dispatch (i : Fin 8) :
    QuotientRankAtLeast (o114SourceU_wc i) (o114SourceLb_wc i) := by
  fin_cases i
  · exact step109wc114s0Dispatch
  · exact step109wc114s1Dispatch
  · exact step109wc114s2Dispatch
  · exact step109wc114s3Dispatch
  · exact step109wc114s4Dispatch
  · exact step109wc114s5Dispatch
  · exact step109wc114s6Dispatch
  · exact step109wc114s7Dispatch

theorem step109_orbit114_lb14_wc : QuotientRankAtLeast o114W_wc 14 :=
  o114Lb14_wc step109wc114_all_dispatch

end QiushiMatmul
