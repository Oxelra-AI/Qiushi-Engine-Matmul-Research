import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit51Consumer
import QiushiOrbit11FP
import QiushiWcOrbit16Dispatch
import QiushiFlattenSeeds

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc51_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc51_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc51s0_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc51s0_contain :
    (o51SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 273) (codeMat 266) orbit11W := by
  change spanCodes [132, 64, 32, 16, 12, 2, 1] ≤ actionW (codeMat 273) (codeMat 266) orbit11W
  apply step109wc51_spanCodes_le_of_gens [132, 64, 32, 16, 12, 2, 1]
    (actionW (codeMat 273) (codeMat 266) orbit11W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 68 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 68 (by decide)
    have hact : actionA (codeMat 273) (codeMat 266) (codeMat 68) = codeMat 132 := by
      unfold actionA
      rw [step109wc51s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 68 * (codeMat 266 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 128 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 128 (by decide)
    have hact : actionA (codeMat 273) (codeMat 266) (codeMat 128) = codeMat 64 := by
      unfold actionA
      rw [step109wc51s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 128 * (codeMat 266 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 32 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 32 (by decide)
    have hact : actionA (codeMat 273) (codeMat 266) (codeMat 32) = codeMat 32 := by
      unfold actionA
      rw [step109wc51s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 32 * (codeMat 266 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 266) (codeMat 8) = codeMat 16 := by
      unfold actionA
      rw [step109wc51s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 266 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 20 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 20 (by decide)
    have hact : actionA (codeMat 273) (codeMat 266) (codeMat 20) = codeMat 12 := by
      unfold actionA
      rw [step109wc51s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 20 * (codeMat 266 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 266) (codeMat 1) = codeMat 2 := by
      unfold actionA
      rw [step109wc51s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 266) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc51s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact

theorem step109wc51s0Dispatch :
    QuotientRankAtLeast (o51SourceU_wc ⟨0, by omega⟩) 12 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 266) orbit11W) 12 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 266) hP hQ orbit11W 12
      orbit11_lb12
  exact quotientRankAtLeast_mono step109wc51s0_contain hAct


private theorem step109wc51s1_QtInv :
    (codeMat 281 : Mat3).transpose⁻¹ = (codeMat 281 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 281 : Mat3).transpose * (codeMat 281 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc51s1_contain :
    (o51SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 273) (codeMat 281) orbit11W := by
  change spanCodes [128, 68, 32, 20, 12, 2, 1] ≤ actionW (codeMat 273) (codeMat 281) orbit11W
  apply step109wc51_spanCodes_le_of_gens [128, 68, 32, 20, 12, 2, 1]
    (actionW (codeMat 273) (codeMat 281) orbit11W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 128 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 128 (by decide)
    have hact : actionA (codeMat 273) (codeMat 281) (codeMat 128) = codeMat 128 := by
      unfold actionA
      rw [step109wc51s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 128 * (codeMat 281 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 196 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 196 (by decide)
    have hact : actionA (codeMat 273) (codeMat 281) (codeMat 196) = codeMat 68 := by
      unfold actionA
      rw [step109wc51s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 196 * (codeMat 281 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 32 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 32 (by decide)
    have hact : actionA (codeMat 273) (codeMat 281) (codeMat 32) = codeMat 32 := by
      unfold actionA
      rw [step109wc51s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 32 * (codeMat 281 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 20 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 20 (by decide)
    have hact : actionA (codeMat 273) (codeMat 281) (codeMat 20) = codeMat 20 := by
      unfold actionA
      rw [step109wc51s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 20 * (codeMat 281 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 28 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 28 (by decide)
    have hact : actionA (codeMat 273) (codeMat 281) (codeMat 28) = codeMat 12 := by
      unfold actionA
      rw [step109wc51s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 28 * (codeMat 281 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 281) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc51s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 281 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 3 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 3 (by decide)
    have hact : actionA (codeMat 273) (codeMat 281) (codeMat 3) = codeMat 1 := by
      unfold actionA
      rw [step109wc51s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 3 * (codeMat 281 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact

theorem step109wc51s1Dispatch :
    QuotientRankAtLeast (o51SourceU_wc ⟨1, by omega⟩) 12 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 281 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 281) orbit11W) 12 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 281) hP hQ orbit11W 12
      orbit11_lb12
  exact quotientRankAtLeast_mono step109wc51s1_contain hAct


private theorem step109wc51s2_QtInv :
    (codeMat 281 : Mat3).transpose⁻¹ = (codeMat 281 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 281 : Mat3).transpose * (codeMat 281 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc51s2_contain :
    (o51SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 161) (codeMat 281) o16W_wc := by
  change spanCodes [256, 148, 80, 32, 12, 2, 1] ≤ actionW (codeMat 161) (codeMat 281) o16W_wc
  apply step109wc51_spanCodes_le_of_gens [256, 148, 80, 32, 12, 2, 1]
    (actionW (codeMat 161) (codeMat 281) o16W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 32 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 161) (codeMat 281) (codeMat 32) = codeMat 256 := by
      unfold actionA
      rw [step109wc51s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 32 * (codeMat 281 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 148 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 148 (by decide)
    have hact : actionA (codeMat 161) (codeMat 281) (codeMat 148) = codeMat 148 := by
      unfold actionA
      rw [step109wc51s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 148 * (codeMat 281 : Mat3).transpose = codeMat 148
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 152 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 152 (by decide)
    have hact : actionA (codeMat 161) (codeMat 281) (codeMat 152) = codeMat 80 := by
      unfold actionA
      rw [step109wc51s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 152 * (codeMat 281 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 161) (codeMat 281) (codeMat 256) = codeMat 32 := by
      unfold actionA
      rw [step109wc51s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 256 * (codeMat 281 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 196 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 196 (by decide)
    have hact : actionA (codeMat 161) (codeMat 281) (codeMat 196) = codeMat 12 := by
      unfold actionA
      rw [step109wc51s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 196 * (codeMat 281 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 281) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc51s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 281 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 3 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 161) (codeMat 281) (codeMat 3) = codeMat 1 := by
      unfold actionA
      rw [step109wc51s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 3 * (codeMat 281 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact

theorem step109wc51s2Dispatch :
    QuotientRankAtLeast (o51SourceU_wc ⟨2, by omega⟩) 12 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 281 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 281) o16W_wc) 12 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 281) hP hQ o16W_wc 12
      step109_orbit16_lb12_wc
  exact quotientRankAtLeast_mono step109wc51s2_contain hAct


private theorem step109wc51s3_QtInv :
    (codeMat 281 : Mat3).transpose⁻¹ = (codeMat 281 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 281 : Mat3).transpose * (codeMat 281 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc51s3_contain :
    (o51SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 169) (codeMat 281) o16W_wc := by
  change spanCodes [260, 148, 80, 32, 12, 2, 1] ≤ actionW (codeMat 169) (codeMat 281) o16W_wc
  apply step109wc51_spanCodes_le_of_gens [260, 148, 80, 32, 12, 2, 1]
    (actionW (codeMat 169) (codeMat 281) o16W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 32 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 169) (codeMat 281) (codeMat 32) = codeMat 260 := by
      unfold actionA
      rw [step109wc51s3_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 32 * (codeMat 281 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 150 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 150 (by decide)
    have hact : actionA (codeMat 169) (codeMat 281) (codeMat 150) = codeMat 148 := by
      unfold actionA
      rw [step109wc51s3_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 150 * (codeMat 281 : Mat3).transpose = codeMat 148
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 155 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 155 (by decide)
    have hact : actionA (codeMat 169) (codeMat 281) (codeMat 155) = codeMat 80 := by
      unfold actionA
      rw [step109wc51s3_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 155 * (codeMat 281 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 169) (codeMat 281) (codeMat 256) = codeMat 32 := by
      unfold actionA
      rw [step109wc51s3_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 256 * (codeMat 281 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 196 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 196 (by decide)
    have hact : actionA (codeMat 169) (codeMat 281) (codeMat 196) = codeMat 12 := by
      unfold actionA
      rw [step109wc51s3_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 196 * (codeMat 281 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 169) (codeMat 281) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc51s3_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 2 * (codeMat 281 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 3 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 169) (codeMat 281) (codeMat 3) = codeMat 1 := by
      unfold actionA
      rw [step109wc51s3_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 3 * (codeMat 281 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact

theorem step109wc51s3Dispatch :
    QuotientRankAtLeast (o51SourceU_wc ⟨3, by omega⟩) 12 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 281 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 281) o16W_wc) 12 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 281) hP hQ o16W_wc 12
      step109_orbit16_lb12_wc
  exact quotientRankAtLeast_mono step109wc51s3_contain hAct


private theorem step109wc51s4_QtInv :
    (codeMat 317 : Mat3).transpose⁻¹ = (codeMat 285 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 317 : Mat3).transpose * (codeMat 285 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc51s4_contain :
    (o51SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 225) (codeMat 317) o16W_wc := by
  change spanCodes [272, 148, 80, 32, 12, 2, 1] ≤ actionW (codeMat 225) (codeMat 317) o16W_wc
  apply step109wc51_spanCodes_le_of_gens [272, 148, 80, 32, 12, 2, 1]
    (actionW (codeMat 225) (codeMat 317) o16W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 186 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 186 (by decide)
    have hact : actionA (codeMat 225) (codeMat 317) (codeMat 186) = codeMat 272 := by
      unfold actionA
      rw [step109wc51s4_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 186 * (codeMat 285 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 149 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 149 (by decide)
    have hact : actionA (codeMat 225) (codeMat 317) (codeMat 149) = codeMat 148 := by
      unfold actionA
      rw [step109wc51s4_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 149 * (codeMat 285 : Mat3).transpose = codeMat 148
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 154 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 154 (by decide)
    have hact : actionA (codeMat 225) (codeMat 317) (codeMat 154) = codeMat 80 := by
      unfold actionA
      rw [step109wc51s4_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 154 * (codeMat 285 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 455 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 455 (by decide)
    have hact : actionA (codeMat 225) (codeMat 317) (codeMat 455) = codeMat 32 := by
      unfold actionA
      rw [step109wc51s4_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 455 * (codeMat 285 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 196 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 196 (by decide)
    have hact : actionA (codeMat 225) (codeMat 317) (codeMat 196) = codeMat 12 := by
      unfold actionA
      rw [step109wc51s4_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 196 * (codeMat 285 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 225) (codeMat 317) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc51s4_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 2 * (codeMat 285 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 3 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 225) (codeMat 317) (codeMat 3) = codeMat 1 := by
      unfold actionA
      rw [step109wc51s4_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 3 * (codeMat 285 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact

theorem step109wc51s4Dispatch :
    QuotientRankAtLeast (o51SourceU_wc ⟨4, by omega⟩) 12 := by
  have hP : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 317 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 225) (codeMat 317) o16W_wc) 12 :=
    @quotientRankAtLeast_action (codeMat 225) (codeMat 317) hP hQ o16W_wc 12
      step109_orbit16_lb12_wc
  exact quotientRankAtLeast_mono step109wc51s4_contain hAct


private theorem step109wc51s5_QtInv :
    (codeMat 317 : Mat3).transpose⁻¹ = (codeMat 285 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 317 : Mat3).transpose * (codeMat 285 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc51s5_contain :
    (o51SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 233) (codeMat 317) o16W_wc := by
  change spanCodes [276, 148, 80, 32, 12, 2, 1] ≤ actionW (codeMat 233) (codeMat 317) o16W_wc
  apply step109wc51_spanCodes_le_of_gens [276, 148, 80, 32, 12, 2, 1]
    (actionW (codeMat 233) (codeMat 317) o16W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 186 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 186 (by decide)
    have hact : actionA (codeMat 233) (codeMat 317) (codeMat 186) = codeMat 276 := by
      unfold actionA
      rw [step109wc51s5_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 186 * (codeMat 285 : Mat3).transpose = codeMat 276
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 151 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 151 (by decide)
    have hact : actionA (codeMat 233) (codeMat 317) (codeMat 151) = codeMat 148 := by
      unfold actionA
      rw [step109wc51s5_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 151 * (codeMat 285 : Mat3).transpose = codeMat 148
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 153 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 153 (by decide)
    have hact : actionA (codeMat 233) (codeMat 317) (codeMat 153) = codeMat 80 := by
      unfold actionA
      rw [step109wc51s5_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 153 * (codeMat 285 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 455 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 455 (by decide)
    have hact : actionA (codeMat 233) (codeMat 317) (codeMat 455) = codeMat 32 := by
      unfold actionA
      rw [step109wc51s5_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 455 * (codeMat 285 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 196 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 196 (by decide)
    have hact : actionA (codeMat 233) (codeMat 317) (codeMat 196) = codeMat 12 := by
      unfold actionA
      rw [step109wc51s5_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 196 * (codeMat 285 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 233) (codeMat 317) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc51s5_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 2 * (codeMat 285 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 3 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 233) (codeMat 317) (codeMat 3) = codeMat 1 := by
      unfold actionA
      rw [step109wc51s5_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 3 * (codeMat 285 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact

theorem step109wc51s5Dispatch :
    QuotientRankAtLeast (o51SourceU_wc ⟨5, by omega⟩) 12 := by
  have hP : Invertible (codeMat 233 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 317 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 233) (codeMat 317) o16W_wc) 12 :=
    @quotientRankAtLeast_action (codeMat 233) (codeMat 317) hP hQ o16W_wc 12
      step109_orbit16_lb12_wc
  exact quotientRankAtLeast_mono step109wc51s5_contain hAct


private theorem step109wc51s6_QtInv :
    (codeMat 163 : Mat3).transpose⁻¹ = (codeMat 165 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 163 : Mat3).transpose * (codeMat 165 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc51s6_contain :
    (o51SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 273) (codeMat 163) flatW_7 := by
  change spanCodes [144, 80, 32, 8, 4, 2, 1] ≤ actionW (codeMat 273) (codeMat 163) flatW_7
  apply step109wc51_spanCodes_le_of_gens [144, 80, 32, 8, 4, 2, 1]
    (actionW (codeMat 273) (codeMat 163) flatW_7)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 360 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 360 (by decide)
    have hact : actionA (codeMat 273) (codeMat 163) (codeMat 360) = codeMat 144 := by
      unfold actionA
      rw [step109wc51s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 360 * (codeMat 165 : Mat3).transpose = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 104 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 104 (by decide)
    have hact : actionA (codeMat 273) (codeMat 163) (codeMat 104) = codeMat 80 := by
      unfold actionA
      rw [step109wc51s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 104 * (codeMat 165 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 16 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 16 (by decide)
    have hact : actionA (codeMat 273) (codeMat 163) (codeMat 16) = codeMat 32 := by
      unfold actionA
      rw [step109wc51s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 16 * (codeMat 165 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 163) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step109wc51s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 165 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 163) (codeMat 2) = codeMat 4 := by
      unfold actionA
      rw [step109wc51s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 165 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 5 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 5 (by decide)
    have hact : actionA (codeMat 273) (codeMat 163) (codeMat 5) = codeMat 2 := by
      unfold actionA
      rw [step109wc51s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 5 * (codeMat 165 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 1 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 163) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc51s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 165 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc51_codeMat_mem_actionW_of_witness hw hact

theorem step109wc51s6Dispatch :
    QuotientRankAtLeast (o51SourceU_wc ⟨6, by omega⟩) 9 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 163 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 163) flatW_7) 9 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 163) hP hQ flatW_7 9
      flatSeed_7
  exact quotientRankAtLeast_mono step109wc51s6_contain hAct

theorem step109wc51_all_dispatch (i : Fin 7) :
    QuotientRankAtLeast (o51SourceU_wc i) (o51SourceLb_wc i) := by
  fin_cases i
  · exact step109wc51s0Dispatch
  · exact step109wc51s1Dispatch
  · exact step109wc51s2Dispatch
  · exact step109wc51s3Dispatch
  · exact step109wc51s4Dispatch
  · exact step109wc51s5Dispatch
  · exact step109wc51s6Dispatch

theorem step109_orbit51_lb14_wc : QuotientRankAtLeast o51W_wc 14 :=
  o51Lb14_wc step109wc51_all_dispatch

end QiushiMatmul
