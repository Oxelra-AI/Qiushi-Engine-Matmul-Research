import Mathlib
import QiushiCodeSpanCore
import QiushiFlattenSeeds
import QiushiMonotonicity
import QiushiOrbit11FP
import QiushiOrbit23FP
import QiushiOrbit31FP
import QiushiOrbit35FP
import QiushiOrbitTransport
import QiushiStep99Orbit55Dispatch
import QiushiTransposeTransport
import QiushiWcOrbit16Dispatch
import QiushiWcOrbit96Dispatch

set_option maxHeartbeats 800000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step113_262_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by intro M hM; rcases hM with ⟨n, hn, rfl⟩; exact h n hn)

private theorem step113_262_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  exact ⟨codeMat witness, h_mem, h_action⟩

private theorem step113_262_codeMat_mem_transposeW_of_witness
    {V : Submodule F2 Mat3} {pre tpre : Nat}
    (h_mem : codeMat tpre ∈ V)
    (h_trans : (codeMat tpre : Mat3).transpose = codeMat pre) :
    codeMat pre ∈ transposeW V := by
  exact ⟨codeMat tpre, h_mem, h_trans⟩

/-- Orbit 262 quotient kernel. -/
def o262W : Submodule F2 Mat3 := spanCodes [132, 12, 2, 1]

-- Source 0: row 38, orbit 23, lb 12, cap 4
def step113_262ActualSource0 : Submodule F2 Mat3 := spanCodes [128, 80, 8, 4, 2, 1]

theorem step113_262_row0_W_le_source : o262W ≤ step113_262ActualSource0 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource0
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [128, 80, 8, 4, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [128, 80, 8, 4, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [128, 80, 8, 4, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [128, 80, 8, 4, 2, 1] 1 (by decide)

private theorem step113_262s0_source_le :
    step113_262ActualSource0 ≤ orbit23W := by
  apply step113_262_spanCodes_le_of_gens [128, 80, 8, 4, 2, 1] orbit23W
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 80, 128] 128 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 80, 128] 80 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 80, 128] 8 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 80, 128] 4 (by decide)
  · subst h4
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 80, 128] 2 (by decide)
  · subst h5
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 80, 128] 1 (by decide)

theorem step113_262_row0_qr : QuotientRankAtLeast step113_262ActualSource0 12 :=
  quotientRankAtLeast_mono step113_262s0_source_le QiushiMatmul.orbit23_lb12

-- Source 1: row 47, orbit 31, lb 15, cap 1
def step113_262ActualSource1 : Submodule F2 Mat3 := spanCodes [132, 32, 16, 12, 2, 1]

theorem step113_262_row1_W_le_source : o262W ≤ step113_262ActualSource1 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource1
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [132, 32, 16, 12, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [132, 32, 16, 12, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [132, 32, 16, 12, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [132, 32, 16, 12, 2, 1] 1 (by decide)

private theorem step113_262s1_QtInv :
    (codeMat 98 : Mat3).transpose⁻¹ = (codeMat 140 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 98 : Mat3).transpose * (codeMat 140 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s1_source_le :
    step113_262ActualSource1 ≤ actionW (codeMat 266) (codeMat 98) orbit31W := by
  apply step113_262_spanCodes_le_of_gens [132, 32, 16, 12, 2, 1]
    (actionW (codeMat 266) (codeMat 98) orbit31W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 80 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 80 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 80) = codeMat 132 := by
      unfold actionA; rw [step113_262s1_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 80 * (codeMat 140 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 2) = codeMat 32 := by
      unfold actionA; rw [step113_262s1_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 140 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 1) = codeMat 16 := by
      unfold actionA; rw [step113_262s1_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 140 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 20 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 20 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 20) = codeMat 12 := by
      unfold actionA; rw [step113_262s1_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 20 * (codeMat 140 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 8) = codeMat 2 := by
      unfold actionA; rw [step113_262s1_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 140 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 32 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 32) = codeMat 1 := by
      unfold actionA; rw [step113_262s1_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 140 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row1_qr : QuotientRankAtLeast step113_262ActualSource1 15 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 98) orbit31W) 15 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 98) hP hQ orbit31W 15 QiushiMatmul.orbit31_lb15
  exact quotientRankAtLeast_mono step113_262s1_source_le hAct

-- Source 2: row 48, orbit 31, lb 15, cap 1
def step113_262ActualSource2 : Submodule F2 Mat3 := spanCodes [132, 36, 16, 12, 2, 1]

theorem step113_262_row2_W_le_source : o262W ≤ step113_262ActualSource2 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource2
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [132, 36, 16, 12, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [132, 36, 16, 12, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [132, 36, 16, 12, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [132, 36, 16, 12, 2, 1] 1 (by decide)

private theorem step113_262s2_QtInv :
    (codeMat 354 : Mat3).transpose⁻¹ = (codeMat 142 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 354 : Mat3).transpose * (codeMat 142 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s2_source_le :
    step113_262ActualSource2 ≤ actionW (codeMat 266) (codeMat 354) orbit31W := by
  apply step113_262_spanCodes_le_of_gens [132, 36, 16, 12, 2, 1]
    (actionW (codeMat 266) (codeMat 354) orbit31W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 112 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 112 (by decide)
    have hact : actionA (codeMat 266) (codeMat 354) (codeMat 112) = codeMat 132 := by
      unfold actionA; rw [step113_262s2_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 112 * (codeMat 142 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 54 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 54 (by decide)
    have hact : actionA (codeMat 266) (codeMat 354) (codeMat 54) = codeMat 36 := by
      unfold actionA; rw [step113_262s2_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 54 * (codeMat 142 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 354) (codeMat 1) = codeMat 16 := by
      unfold actionA; rw [step113_262s2_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 142 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 52 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 52 (by decide)
    have hact : actionA (codeMat 266) (codeMat 354) (codeMat 52) = codeMat 12 := by
      unfold actionA; rw [step113_262s2_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 52 * (codeMat 142 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 354) (codeMat 8) = codeMat 2 := by
      unfold actionA; rw [step113_262s2_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 142 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 32 (by decide)
    have hact : actionA (codeMat 266) (codeMat 354) (codeMat 32) = codeMat 1 := by
      unfold actionA; rw [step113_262s2_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 142 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row2_qr : QuotientRankAtLeast step113_262ActualSource2 15 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 354 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 354) orbit31W) 15 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 354) hP hQ orbit31W 15 QiushiMatmul.orbit31_lb15
  exact quotientRankAtLeast_mono step113_262s2_source_le hAct

-- Source 3: row 52, orbit 31, lb 15, cap 1
def step113_262ActualSource3 : Submodule F2 Mat3 := spanCodes [256, 132, 64, 12, 2, 1]

theorem step113_262_row3_W_le_source : o262W ≤ step113_262ActualSource3 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource3
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 12, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 12, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 12, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 12, 2, 1] 1 (by decide)

private theorem step113_262s3_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s3_source_le :
    step113_262ActualSource3 ≤ actionW (codeMat 140) (codeMat 161) orbit31W := by
  apply step113_262_spanCodes_le_of_gens [256, 132, 64, 12, 2, 1]
    (actionW (codeMat 140) (codeMat 161) orbit31W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 2 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 2 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 2) = codeMat 256 := by
      unfold actionA; rw [step113_262s3_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 2 * (codeMat 161 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 20 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 20 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 20) = codeMat 132 := by
      unfold actionA; rw [step113_262s3_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 20 * (codeMat 161 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 1 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 1) = codeMat 64 := by
      unfold actionA; rw [step113_262s3_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 80 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 80 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 80) = codeMat 12 := by
      unfold actionA; rw [step113_262s3_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 80 * (codeMat 161 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 32 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 32 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 32) = codeMat 2 := by
      unfold actionA; rw [step113_262s3_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 32 * (codeMat 161 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 8 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 8) = codeMat 1 := by
      unfold actionA; rw [step113_262s3_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 8 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row3_qr : QuotientRankAtLeast step113_262ActualSource3 15 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 161) orbit31W) 15 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 161) hP hQ orbit31W 15 QiushiMatmul.orbit31_lb15
  exact quotientRankAtLeast_mono step113_262s3_source_le hAct

-- Source 4: row 53, orbit 31, lb 15, cap 1
def step113_262ActualSource4 : Submodule F2 Mat3 := spanCodes [260, 132, 64, 12, 2, 1]

theorem step113_262_row4_W_le_source : o262W ≤ step113_262ActualSource4 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource4
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 132, 64, 12, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 132, 64, 12, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 132, 64, 12, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 132, 64, 12, 2, 1] 1 (by decide)

private theorem step113_262s4_QtInv :
    (codeMat 417 : Mat3).transpose⁻¹ = (codeMat 177 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 417 : Mat3).transpose * (codeMat 177 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s4_source_le :
    step113_262ActualSource4 ≤ actionW (codeMat 140) (codeMat 417) orbit31W := by
  apply step113_262_spanCodes_le_of_gens [260, 132, 64, 12, 2, 1]
    (actionW (codeMat 140) (codeMat 417) orbit31W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 54 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 54 (by decide)
    have hact : actionA (codeMat 140) (codeMat 417) (codeMat 54) = codeMat 260 := by
      unfold actionA; rw [step113_262s4_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 54 * (codeMat 177 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 52 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 52 (by decide)
    have hact : actionA (codeMat 140) (codeMat 417) (codeMat 52) = codeMat 132 := by
      unfold actionA; rw [step113_262s4_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 52 * (codeMat 177 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 1 (by decide)
    have hact : actionA (codeMat 140) (codeMat 417) (codeMat 1) = codeMat 64 := by
      unfold actionA; rw [step113_262s4_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 1 * (codeMat 177 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 112 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 112 (by decide)
    have hact : actionA (codeMat 140) (codeMat 417) (codeMat 112) = codeMat 12 := by
      unfold actionA; rw [step113_262s4_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 112 * (codeMat 177 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 32 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 32 (by decide)
    have hact : actionA (codeMat 140) (codeMat 417) (codeMat 32) = codeMat 2 := by
      unfold actionA; rw [step113_262s4_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 32 * (codeMat 177 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 8 (by decide)
    have hact : actionA (codeMat 140) (codeMat 417) (codeMat 8) = codeMat 1 := by
      unfold actionA; rw [step113_262s4_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 8 * (codeMat 177 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row4_qr : QuotientRankAtLeast step113_262ActualSource4 15 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 417) orbit31W) 15 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 417) hP hQ orbit31W 15 QiushiMatmul.orbit31_lb15
  exact quotientRankAtLeast_mono step113_262s4_source_le hAct

-- Source 5: row 78, orbit 35, lb 15, cap 1
def step113_262ActualSource5 : Submodule F2 Mat3 := spanCodes [132, 100, 20, 12, 2, 1]

theorem step113_262_row5_W_le_source : o262W ≤ step113_262ActualSource5 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource5
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [132, 100, 20, 12, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [132, 100, 20, 12, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [132, 100, 20, 12, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [132, 100, 20, 12, 2, 1] 1 (by decide)

private theorem step113_262s5_QtInv :
    (codeMat 281 : Mat3).transpose⁻¹ = (codeMat 281 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 281 : Mat3).transpose * (codeMat 281 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s5_source_le :
    step113_262ActualSource5 ≤ actionW (codeMat 401) (codeMat 281) orbit35W := by
  apply step113_262_spanCodes_le_of_gens [132, 100, 20, 12, 2, 1]
    (actionW (codeMat 401) (codeMat 281) orbit35W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 148 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 148 (by decide)
    have hact : actionA (codeMat 401) (codeMat 281) (codeMat 148) = codeMat 132 := by
      unfold actionA; rw [step113_262s5_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 148 * (codeMat 281 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 252 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 252 (by decide)
    have hact : actionA (codeMat 401) (codeMat 281) (codeMat 252) = codeMat 100 := by
      unfold actionA; rw [step113_262s5_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 252 * (codeMat 281 : Mat3).transpose = codeMat 100
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 20 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 20 (by decide)
    have hact : actionA (codeMat 401) (codeMat 281) (codeMat 20) = codeMat 20 := by
      unfold actionA; rw [step113_262s5_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 20 * (codeMat 281 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 28 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 28 (by decide)
    have hact : actionA (codeMat 401) (codeMat 281) (codeMat 28) = codeMat 12 := by
      unfold actionA; rw [step113_262s5_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 28 * (codeMat 281 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 2 (by decide)
    have hact : actionA (codeMat 401) (codeMat 281) (codeMat 2) = codeMat 2 := by
      unfold actionA; rw [step113_262s5_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 2 * (codeMat 281 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 3 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 3 (by decide)
    have hact : actionA (codeMat 401) (codeMat 281) (codeMat 3) = codeMat 1 := by
      unfold actionA; rw [step113_262s5_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 3 * (codeMat 281 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row5_qr : QuotientRankAtLeast step113_262ActualSource5 15 := by
  have hP : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 281 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 401) (codeMat 281) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 401) (codeMat 281) hP hQ orbit35W 15 QiushiMatmul.orbit35_lb15
  exact quotientRankAtLeast_mono step113_262s5_source_le hAct

-- Source 6: row 79, orbit 35, lb 15, cap 1
def step113_262ActualSource6 : Submodule F2 Mat3 := spanCodes [132, 96, 20, 12, 2, 1]

theorem step113_262_row6_W_le_source : o262W ≤ step113_262ActualSource6 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource6
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [132, 96, 20, 12, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [132, 96, 20, 12, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [132, 96, 20, 12, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [132, 96, 20, 12, 2, 1] 1 (by decide)

private theorem step113_262s6_QtInv :
    (codeMat 313 : Mat3).transpose⁻¹ = (codeMat 313 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 313 : Mat3).transpose * (codeMat 313 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s6_source_le :
    step113_262ActualSource6 ≤ actionW (codeMat 401) (codeMat 313) orbit35W := by
  apply step113_262_spanCodes_le_of_gens [132, 96, 20, 12, 2, 1]
    (actionW (codeMat 401) (codeMat 313) orbit35W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 150 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 150 (by decide)
    have hact : actionA (codeMat 401) (codeMat 313) (codeMat 150) = codeMat 132 := by
      unfold actionA; rw [step113_262s6_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 150 * (codeMat 313 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 232 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 232 (by decide)
    have hact : actionA (codeMat 401) (codeMat 313) (codeMat 232) = codeMat 96 := by
      unfold actionA; rw [step113_262s6_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 232 * (codeMat 313 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 22 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 22 (by decide)
    have hact : actionA (codeMat 401) (codeMat 313) (codeMat 22) = codeMat 20 := by
      unfold actionA; rw [step113_262s6_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 22 * (codeMat 313 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 30 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 30 (by decide)
    have hact : actionA (codeMat 401) (codeMat 313) (codeMat 30) = codeMat 12 := by
      unfold actionA; rw [step113_262s6_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 30 * (codeMat 313 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 2 (by decide)
    have hact : actionA (codeMat 401) (codeMat 313) (codeMat 2) = codeMat 2 := by
      unfold actionA; rw [step113_262s6_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 2 * (codeMat 313 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 3 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 3 (by decide)
    have hact : actionA (codeMat 401) (codeMat 313) (codeMat 3) = codeMat 1 := by
      unfold actionA; rw [step113_262s6_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 3 * (codeMat 313 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row6_qr : QuotientRankAtLeast step113_262ActualSource6 15 := by
  have hP : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 313 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 401) (codeMat 313) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 401) (codeMat 313) hP hQ orbit35W 15 QiushiMatmul.orbit35_lb15
  exact quotientRankAtLeast_mono step113_262s6_source_le hAct

-- Source 7: row 80, orbit 35, lb 15, cap 1
def step113_262ActualSource7 : Submodule F2 Mat3 := spanCodes [276, 132, 68, 12, 2, 1]

theorem step113_262_row7_W_le_source : o262W ≤ step113_262ActualSource7 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource7
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [276, 132, 68, 12, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [276, 132, 68, 12, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [276, 132, 68, 12, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [276, 132, 68, 12, 2, 1] 1 (by decide)

private theorem step113_262s7_QtInv :
    (codeMat 282 : Mat3).transpose⁻¹ = (codeMat 267 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 282 : Mat3).transpose * (codeMat 267 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s7_source_le :
    step113_262ActualSource7 ≤ actionW (codeMat 417) (codeMat 282) orbit35W := by
  apply step113_262_spanCodes_le_of_gens [276, 132, 68, 12, 2, 1]
    (actionW (codeMat 417) (codeMat 282) orbit35W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 252 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 252 (by decide)
    have hact : actionA (codeMat 417) (codeMat 282) (codeMat 252) = codeMat 276 := by
      unfold actionA; rw [step113_262s7_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 252 * (codeMat 267 : Mat3).transpose = codeMat 276
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 28 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 28 (by decide)
    have hact : actionA (codeMat 417) (codeMat 282) (codeMat 28) = codeMat 132 := by
      unfold actionA; rw [step113_262s7_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 28 * (codeMat 267 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 20 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 20 (by decide)
    have hact : actionA (codeMat 417) (codeMat 282) (codeMat 20) = codeMat 68 := by
      unfold actionA; rw [step113_262s7_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 20 * (codeMat 267 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 148 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 148 (by decide)
    have hact : actionA (codeMat 417) (codeMat 282) (codeMat 148) = codeMat 12 := by
      unfold actionA; rw [step113_262s7_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 148 * (codeMat 267 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 3 (by decide)
    have hact : actionA (codeMat 417) (codeMat 282) (codeMat 3) = codeMat 2 := by
      unfold actionA; rw [step113_262s7_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 3 * (codeMat 267 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 2 (by decide)
    have hact : actionA (codeMat 417) (codeMat 282) (codeMat 2) = codeMat 1 := by
      unfold actionA; rw [step113_262s7_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 2 * (codeMat 267 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row7_qr : QuotientRankAtLeast step113_262ActualSource7 15 := by
  have hP : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 282 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 417) (codeMat 282) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 417) (codeMat 282) hP hQ orbit35W 15 QiushiMatmul.orbit35_lb15
  exact quotientRankAtLeast_mono step113_262s7_source_le hAct

-- Source 8: row 81, orbit 35, lb 15, cap 1
def step113_262ActualSource8 : Submodule F2 Mat3 := spanCodes [272, 132, 68, 12, 2, 1]

theorem step113_262_row8_W_le_source : o262W ≤ step113_262ActualSource8 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource8
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 132, 68, 12, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 132, 68, 12, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 132, 68, 12, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 132, 68, 12, 2, 1] 1 (by decide)

private theorem step113_262s8_QtInv :
    (codeMat 314 : Mat3).transpose⁻¹ = (codeMat 271 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 314 : Mat3).transpose * (codeMat 271 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s8_source_le :
    step113_262ActualSource8 ≤ actionW (codeMat 417) (codeMat 314) orbit35W := by
  apply step113_262_spanCodes_le_of_gens [272, 132, 68, 12, 2, 1]
    (actionW (codeMat 417) (codeMat 314) orbit35W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 232 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 232 (by decide)
    have hact : actionA (codeMat 417) (codeMat 314) (codeMat 232) = codeMat 272 := by
      unfold actionA; rw [step113_262s8_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 232 * (codeMat 271 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 30 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 30 (by decide)
    have hact : actionA (codeMat 417) (codeMat 314) (codeMat 30) = codeMat 132 := by
      unfold actionA; rw [step113_262s8_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 30 * (codeMat 271 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 22 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 22 (by decide)
    have hact : actionA (codeMat 417) (codeMat 314) (codeMat 22) = codeMat 68 := by
      unfold actionA; rw [step113_262s8_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 22 * (codeMat 271 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 150 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 150 (by decide)
    have hact : actionA (codeMat 417) (codeMat 314) (codeMat 150) = codeMat 12 := by
      unfold actionA; rw [step113_262s8_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 150 * (codeMat 271 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 3 (by decide)
    have hact : actionA (codeMat 417) (codeMat 314) (codeMat 3) = codeMat 2 := by
      unfold actionA; rw [step113_262s8_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 3 * (codeMat 271 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 2 (by decide)
    have hact : actionA (codeMat 417) (codeMat 314) (codeMat 2) = codeMat 1 := by
      unfold actionA; rw [step113_262s8_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 2 * (codeMat 271 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row8_qr : QuotientRankAtLeast step113_262ActualSource8 15 := by
  have hP : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 314 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 417) (codeMat 314) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 417) (codeMat 314) hP hQ orbit35W 15 QiushiMatmul.orbit35_lb15
  exact quotientRankAtLeast_mono step113_262s8_source_le hAct

-- Source 9: row 82, orbit 35, lb 15, cap 1
def step113_262ActualSource9 : Submodule F2 Mat3 := spanCodes [304, 132, 80, 12, 2, 1]

theorem step113_262_row9_W_le_source : o262W ≤ step113_262ActualSource9 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource9
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [304, 132, 80, 12, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [304, 132, 80, 12, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [304, 132, 80, 12, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [304, 132, 80, 12, 2, 1] 1 (by decide)

private theorem step113_262s9_QtInv :
    (codeMat 419 : Mat3).transpose⁻¹ = (codeMat 183 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 419 : Mat3).transpose * (codeMat 183 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s9_source_le :
    step113_262ActualSource9 ≤ transposeW (actionW (codeMat 331) (codeMat 419) orbit35W) := by
  apply step113_262_spanCodes_le_of_gens [304, 132, 80, 12, 2, 1]
    (transposeW (actionW (codeMat 331) (codeMat 419) orbit35W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 245 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 245 (by decide)
    have hact : actionA (codeMat 331) (codeMat 419) (codeMat 245) = codeMat 400 := by
      unfold actionA; rw [step113_262s9_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 245 * (codeMat 183 : Mat3).transpose = codeMat 400
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 400 ∈ actionW (codeMat 331) (codeMat 419) orbit35W :=
      step113_262_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 400 : Mat3).transpose = codeMat 304 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h1
    have hw : codeMat 126 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 126 (by decide)
    have hact : actionA (codeMat 331) (codeMat 419) (codeMat 126) = codeMat 96 := by
      unfold actionA; rw [step113_262s9_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 126 * (codeMat 183 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 96 ∈ actionW (codeMat 331) (codeMat 419) orbit35W :=
      step113_262_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 96 : Mat3).transpose = codeMat 132 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h2
    have hw : codeMat 29 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 29 (by decide)
    have hact : actionA (codeMat 331) (codeMat 419) (codeMat 29) = codeMat 20 := by
      unfold actionA; rw [step113_262s9_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 29 * (codeMat 183 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 20 ∈ actionW (codeMat 331) (codeMat 419) orbit35W :=
      step113_262_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 20 : Mat3).transpose = codeMat 80 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h3
    have hw : codeMat 96 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 96 (by decide)
    have hact : actionA (codeMat 331) (codeMat 419) (codeMat 96) = codeMat 66 := by
      unfold actionA; rw [step113_262s9_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 96 * (codeMat 183 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 66 ∈ actionW (codeMat 331) (codeMat 419) orbit35W :=
      step113_262_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 66 : Mat3).transpose = codeMat 12 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h4
    have hw : codeMat 9 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 9 (by decide)
    have hact : actionA (codeMat 331) (codeMat 419) (codeMat 9) = codeMat 8 := by
      unfold actionA; rw [step113_262s9_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 9 * (codeMat 183 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 8 ∈ actionW (codeMat 331) (codeMat 419) orbit35W :=
      step113_262_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 8 : Mat3).transpose = codeMat 2 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h5
    have hw : codeMat 8 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 8 (by decide)
    have hact : actionA (codeMat 331) (codeMat 419) (codeMat 8) = codeMat 1 := by
      unfold actionA; rw [step113_262s9_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 8 * (codeMat 183 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 1 ∈ actionW (codeMat 331) (codeMat 419) orbit35W :=
      step113_262_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 1 : Mat3).transpose = codeMat 1 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_transposeW_of_witness hmA htrans

theorem step113_262_row9_qr : QuotientRankAtLeast step113_262ActualSource9 15 := by
  have hP : Invertible (codeMat 331 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 419 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 331) (codeMat 419) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 331) (codeMat 419) hP hQ orbit35W 15 QiushiMatmul.orbit35_lb15
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 331) (codeMat 419) orbit35W)) 15 :=
    quotientRankAtLeast_transpose hAct
  exact quotientRankAtLeast_mono step113_262s9_source_le hT

-- Source 10: row 84, orbit 35, lb 15, cap 1
def step113_262ActualSource10 : Submodule F2 Mat3 := spanCodes [288, 132, 80, 12, 2, 1]

theorem step113_262_row10_W_le_source : o262W ≤ step113_262ActualSource10 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource10
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 132, 80, 12, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 132, 80, 12, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 132, 80, 12, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 132, 80, 12, 2, 1] 1 (by decide)

private theorem step113_262s10_QtInv :
    (codeMat 417 : Mat3).transpose⁻¹ = (codeMat 177 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 417 : Mat3).transpose * (codeMat 177 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s10_source_le :
    step113_262ActualSource10 ≤ transposeW (actionW (codeMat 267) (codeMat 417) orbit35W) := by
  apply step113_262_spanCodes_le_of_gens [288, 132, 80, 12, 2, 1]
    (transposeW (actionW (codeMat 267) (codeMat 417) orbit35W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 128 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 128 (by decide)
    have hact : actionA (codeMat 267) (codeMat 417) (codeMat 128) = codeMat 384 := by
      unfold actionA; rw [step113_262s10_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 128 * (codeMat 177 : Mat3).transpose = codeMat 384
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 384 ∈ actionW (codeMat 267) (codeMat 417) orbit35W :=
      step113_262_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 384 : Mat3).transpose = codeMat 288 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h1
    have hw : codeMat 118 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 118 (by decide)
    have hact : actionA (codeMat 267) (codeMat 417) (codeMat 118) = codeMat 96 := by
      unfold actionA; rw [step113_262s10_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 118 * (codeMat 177 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 96 ∈ actionW (codeMat 267) (codeMat 417) orbit35W :=
      step113_262_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 96 : Mat3).transpose = codeMat 132 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h2
    have hw : codeMat 20 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 20 (by decide)
    have hact : actionA (codeMat 267) (codeMat 417) (codeMat 20) = codeMat 20 := by
      unfold actionA; rw [step113_262s10_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 20 * (codeMat 177 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 20 ∈ actionW (codeMat 267) (codeMat 417) orbit35W :=
      step113_262_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 20 : Mat3).transpose = codeMat 80 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h3
    have hw : codeMat 96 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 96 (by decide)
    have hact : actionA (codeMat 267) (codeMat 417) (codeMat 96) = codeMat 66 := by
      unfold actionA; rw [step113_262s10_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 96 * (codeMat 177 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 66 ∈ actionW (codeMat 267) (codeMat 417) orbit35W :=
      step113_262_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 66 : Mat3).transpose = codeMat 12 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h4
    have hw : codeMat 9 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 9 (by decide)
    have hact : actionA (codeMat 267) (codeMat 417) (codeMat 9) = codeMat 8 := by
      unfold actionA; rw [step113_262s10_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 9 * (codeMat 177 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 8 ∈ actionW (codeMat 267) (codeMat 417) orbit35W :=
      step113_262_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 8 : Mat3).transpose = codeMat 2 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h5
    have hw : codeMat 8 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 8 (by decide)
    have hact : actionA (codeMat 267) (codeMat 417) (codeMat 8) = codeMat 1 := by
      unfold actionA; rw [step113_262s10_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 8 * (codeMat 177 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 1 ∈ actionW (codeMat 267) (codeMat 417) orbit35W :=
      step113_262_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 1 : Mat3).transpose = codeMat 1 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_transposeW_of_witness hmA htrans

theorem step113_262_row10_qr : QuotientRankAtLeast step113_262ActualSource10 15 := by
  have hP : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 267) (codeMat 417) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 267) (codeMat 417) hP hQ orbit35W 15 QiushiMatmul.orbit35_lb15
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 267) (codeMat 417) orbit35W)) 15 :=
    quotientRankAtLeast_transpose hAct
  exact quotientRankAtLeast_mono step113_262s10_source_le hT

-- Source 11: row 130, orbit 55, lb 14, cap 2
def step113_262ActualSource11 : Submodule F2 Mat3 := spanCodes [272, 132, 32, 12, 2, 1]

theorem step113_262_row11_W_le_source : o262W ≤ step113_262ActualSource11 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource11
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 1 (by decide)

private theorem step113_262s11_source_le :
    step113_262ActualSource11 ≤ o55W := by
  apply step113_262_spanCodes_le_of_gens [272, 132, 32, 12, 2, 1] o55W
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 272 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 132 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 32 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 12 (by decide)
  · subst h4
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 2 (by decide)
  · subst h5
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 1 (by decide)

theorem step113_262_row11_qr : QuotientRankAtLeast step113_262ActualSource11 14 :=
  quotientRankAtLeast_mono step113_262s11_source_le QiushiMatmul.step99_orbit55_lb14_unconditional

-- Source 12: row 131, orbit 55, lb 14, cap 2
def step113_262ActualSource12 : Submodule F2 Mat3 := spanCodes [276, 132, 36, 12, 2, 1]

theorem step113_262_row12_W_le_source : o262W ≤ step113_262ActualSource12 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource12
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [276, 132, 36, 12, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [276, 132, 36, 12, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [276, 132, 36, 12, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [276, 132, 36, 12, 2, 1] 1 (by decide)

private theorem step113_262s12_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s12_source_le :
    step113_262ActualSource12 ≤ actionW (codeMat 345) (codeMat 273) o55W := by
  apply step113_262_spanCodes_le_of_gens [276, 132, 36, 12, 2, 1]
    (actionW (codeMat 345) (codeMat 273) o55W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 274 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 274 (by decide)
    have hact : actionA (codeMat 345) (codeMat 273) (codeMat 274) = codeMat 276 := by
      unfold actionA; rw [step113_262s12_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 274 * (codeMat 273 : Mat3).transpose = codeMat 276
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 134 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 134 (by decide)
    have hact : actionA (codeMat 345) (codeMat 273) (codeMat 134) = codeMat 132 := by
      unfold actionA; rw [step113_262s12_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 134 * (codeMat 273 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 32 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 345) (codeMat 273) (codeMat 32) = codeMat 36 := by
      unfold actionA; rw [step113_262s12_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 32 * (codeMat 273 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 13 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 13 (by decide)
    have hact : actionA (codeMat 345) (codeMat 273) (codeMat 13) = codeMat 12 := by
      unfold actionA; rw [step113_262s12_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 13 * (codeMat 273 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 345) (codeMat 273) (codeMat 2) = codeMat 2 := by
      unfold actionA; rw [step113_262s12_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 345) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA; rw [step113_262s12_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row12_qr : QuotientRankAtLeast step113_262ActualSource12 14 := by
  have hP : Invertible (codeMat 345 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 345) (codeMat 273) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 345) (codeMat 273) hP hQ o55W 14 QiushiMatmul.step99_orbit55_lb14_unconditional
  exact quotientRankAtLeast_mono step113_262s12_source_le hAct

-- Source 13: row 181, orbit 7, lb 9, cap 7
def step113_262ActualSource13 : Submodule F2 Mat3 := spanCodes [272, 128, 48, 8, 4, 2, 1]

theorem step113_262_row13_W_le_source : o262W ≤ step113_262ActualSource13 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource13
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 128, 48, 8, 4, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 128, 48, 8, 4, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 128, 48, 8, 4, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 128, 48, 8, 4, 2, 1] 1 (by decide)

private theorem step113_262s13_QtInv :
    (codeMat 396 : Mat3).transpose⁻¹ = (codeMat 106 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 396 : Mat3).transpose * (codeMat 106 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s13_source_le :
    step113_262ActualSource13 ≤ actionW (codeMat 273) (codeMat 396) flatW_7 := by
  apply step113_262_spanCodes_le_of_gens [272, 128, 48, 8, 4, 2, 1]
    (actionW (codeMat 273) (codeMat 396) flatW_7)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 352 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 352 (by decide)
    have hact : actionA (codeMat 273) (codeMat 396) (codeMat 352) = codeMat 272 := by
      unfold actionA; rw [step113_262s13_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 352 * (codeMat 106 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 256 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 273) (codeMat 396) (codeMat 256) = codeMat 128 := by
      unfold actionA; rw [step113_262s13_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 256 * (codeMat 106 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 396) (codeMat 8) = codeMat 48 := by
      unfold actionA; rw [step113_262s13_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 106 : Mat3).transpose = codeMat 48
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 16 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 16 (by decide)
    have hact : actionA (codeMat 273) (codeMat 396) (codeMat 16) = codeMat 8 := by
      unfold actionA; rw [step113_262s13_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 16 * (codeMat 106 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 5 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 5 (by decide)
    have hact : actionA (codeMat 273) (codeMat 396) (codeMat 5) = codeMat 4 := by
      unfold actionA; rw [step113_262s13_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 5 * (codeMat 106 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 4 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 4 (by decide)
    have hact : actionA (codeMat 273) (codeMat 396) (codeMat 4) = codeMat 2 := by
      unfold actionA; rw [step113_262s13_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 4 * (codeMat 106 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 396) (codeMat 2) = codeMat 1 := by
      unfold actionA; rw [step113_262s13_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 106 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row13_qr : QuotientRankAtLeast step113_262ActualSource13 9 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 396 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 396) flatW_7) 9 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 396) hP hQ flatW_7 9 QiushiMatmul.flatSeed_7
  exact quotientRankAtLeast_mono step113_262s13_source_le hAct

-- Source 14: row 182, orbit 7, lb 9, cap 7
def step113_262ActualSource14 : Submodule F2 Mat3 := spanCodes [272, 128, 32, 8, 4, 2, 1]

theorem step113_262_row14_W_le_source : o262W ≤ step113_262ActualSource14 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource14
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 4, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 4, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 4, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 4, 2, 1] 1 (by decide)

private theorem step113_262s14_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s14_source_le :
    step113_262ActualSource14 ≤ actionW (codeMat 273) (codeMat 140) flatW_7 := by
  apply step113_262_spanCodes_le_of_gens [272, 128, 32, 8, 4, 2, 1]
    (actionW (codeMat 273) (codeMat 140) flatW_7)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 96 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 96 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 96) = codeMat 272 := by
      unfold actionA; rw [step113_262s14_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 96 * (codeMat 98 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 256 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 256) = codeMat 128 := by
      unfold actionA; rw [step113_262s14_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 256 * (codeMat 98 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 8) = codeMat 32 := by
      unfold actionA; rw [step113_262s14_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 16 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 16 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 16) = codeMat 8 := by
      unfold actionA; rw [step113_262s14_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 16 * (codeMat 98 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 1) = codeMat 4 := by
      unfold actionA; rw [step113_262s14_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 4 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 4 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 4) = codeMat 2 := by
      unfold actionA; rw [step113_262s14_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 4 * (codeMat 98 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 2) = codeMat 1 := by
      unfold actionA; rw [step113_262s14_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row14_qr : QuotientRankAtLeast step113_262ActualSource14 9 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 140) flatW_7) 9 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 140) hP hQ flatW_7 9 QiushiMatmul.flatSeed_7
  exact quotientRankAtLeast_mono step113_262s14_source_le hAct

-- Source 15: row 297, orbit 16, lb 12, cap 4
def step113_262ActualSource15 : Submodule F2 Mat3 := spanCodes [276, 132, 84, 32, 12, 2, 1]

theorem step113_262_row15_W_le_source : o262W ≤ step113_262ActualSource15 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource15
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [276, 132, 84, 32, 12, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [276, 132, 84, 32, 12, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [276, 132, 84, 32, 12, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [276, 132, 84, 32, 12, 2, 1] 1 (by decide)

private theorem step113_262s15_QtInv :
    (codeMat 303 : Mat3).transpose⁻¹ = (codeMat 286 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 303 : Mat3).transpose * (codeMat 286 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s15_source_le :
    step113_262ActualSource15 ≤ actionW (codeMat 225) (codeMat 303) o16W_wc := by
  apply step113_262_spanCodes_le_of_gens [276, 132, 84, 32, 12, 2, 1]
    (actionW (codeMat 225) (codeMat 303) o16W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 126 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 126 (by decide)
    have hact : actionA (codeMat 225) (codeMat 303) (codeMat 126) = codeMat 276 := by
      unfold actionA; rw [step113_262s15_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 126 * (codeMat 286 : Mat3).transpose = codeMat 276
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 15 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 15 (by decide)
    have hact : actionA (codeMat 225) (codeMat 303) (codeMat 15) = codeMat 132 := by
      unfold actionA; rw [step113_262s15_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 15 * (codeMat 286 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 94 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 94 (by decide)
    have hact : actionA (codeMat 225) (codeMat 303) (codeMat 94) = codeMat 84 := by
      unfold actionA; rw [step113_262s15_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 94 * (codeMat 286 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 455 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 455 (by decide)
    have hact : actionA (codeMat 225) (codeMat 303) (codeMat 455) = codeMat 32 := by
      unfold actionA; rw [step113_262s15_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 455 * (codeMat 286 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 196 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 196 (by decide)
    have hact : actionA (codeMat 225) (codeMat 303) (codeMat 196) = codeMat 12 := by
      unfold actionA; rw [step113_262s15_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 196 * (codeMat 286 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 225) (codeMat 303) (codeMat 1) = codeMat 2 := by
      unfold actionA; rw [step113_262s15_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 1 * (codeMat 286 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 3 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 225) (codeMat 303) (codeMat 3) = codeMat 1 := by
      unfold actionA; rw [step113_262s15_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 3 * (codeMat 286 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row15_qr : QuotientRankAtLeast step113_262ActualSource15 12 := by
  have hP : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 303 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 225) (codeMat 303) o16W_wc) 12 :=
    @quotientRankAtLeast_action (codeMat 225) (codeMat 303) hP hQ o16W_wc 12 QiushiMatmul.step109_orbit16_lb12_wc
  exact quotientRankAtLeast_mono step113_262s15_source_le hAct

-- Source 16: row 298, orbit 16, lb 12, cap 4
def step113_262ActualSource16 : Submodule F2 Mat3 := spanCodes [272, 132, 84, 36, 12, 2, 1]

theorem step113_262_row16_W_le_source : o262W ≤ step113_262ActualSource16 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource16
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 132, 84, 36, 12, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 132, 84, 36, 12, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 132, 84, 36, 12, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 132, 84, 36, 12, 2, 1] 1 (by decide)

private theorem step113_262s16_QtInv :
    (codeMat 303 : Mat3).transpose⁻¹ = (codeMat 286 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 303 : Mat3).transpose * (codeMat 286 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s16_source_le :
    step113_262ActualSource16 ≤ actionW (codeMat 169) (codeMat 303) o16W_wc := by
  apply step113_262_spanCodes_le_of_gens [272, 132, 84, 36, 12, 2, 1]
    (actionW (codeMat 169) (codeMat 303) o16W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 127 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 127 (by decide)
    have hact : actionA (codeMat 169) (codeMat 303) (codeMat 127) = codeMat 272 := by
      unfold actionA; rw [step113_262s16_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 127 * (codeMat 286 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 14 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 14 (by decide)
    have hact : actionA (codeMat 169) (codeMat 303) (codeMat 14) = codeMat 132 := by
      unfold actionA; rw [step113_262s16_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 14 * (codeMat 286 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 92 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 92 (by decide)
    have hact : actionA (codeMat 169) (codeMat 303) (codeMat 92) = codeMat 84 := by
      unfold actionA; rw [step113_262s16_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 92 * (codeMat 286 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 455 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 455 (by decide)
    have hact : actionA (codeMat 169) (codeMat 303) (codeMat 455) = codeMat 36 := by
      unfold actionA; rw [step113_262s16_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 455 * (codeMat 286 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 199 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 199 (by decide)
    have hact : actionA (codeMat 169) (codeMat 303) (codeMat 199) = codeMat 12 := by
      unfold actionA; rw [step113_262s16_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 199 * (codeMat 286 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 303) (codeMat 1) = codeMat 2 := by
      unfold actionA; rw [step113_262s16_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * (codeMat 286 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 3 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 169) (codeMat 303) (codeMat 3) = codeMat 1 := by
      unfold actionA; rw [step113_262s16_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 3 * (codeMat 286 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row16_qr : QuotientRankAtLeast step113_262ActualSource16 12 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 303 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 303) o16W_wc) 12 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 303) hP hQ o16W_wc 12 QiushiMatmul.step109_orbit16_lb12_wc
  exact quotientRankAtLeast_mono step113_262s16_source_le hAct

-- Source 17: row 320, orbit 2, lb 6, cap 10
def step113_262ActualSource17 : Submodule F2 Mat3 := spanCodes [288, 128, 96, 16, 8, 4, 2, 1]

theorem step113_262_row17_W_le_source : o262W ≤ step113_262ActualSource17 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource17
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 128, 96, 16, 8, 4, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 128, 96, 16, 8, 4, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 128, 96, 16, 8, 4, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 128, 96, 16, 8, 4, 2, 1] 1 (by decide)

private theorem step113_262s17_QtInv :
    (codeMat 354 : Mat3).transpose⁻¹ = (codeMat 142 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 354 : Mat3).transpose * (codeMat 142 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s17_source_le :
    step113_262ActualSource17 ≤ actionW (codeMat 161) (codeMat 354) flatW_2 := by
  apply step113_262_spanCodes_le_of_gens [288, 128, 96, 16, 8, 4, 2, 1]
    (actionW (codeMat 161) (codeMat 354) flatW_2)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 432 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 432 (by decide)
    have hact : actionA (codeMat 161) (codeMat 354) (codeMat 432) = codeMat 288 := by
      unfold actionA; rw [step113_262s17_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 432 * (codeMat 142 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 8 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 161) (codeMat 354) (codeMat 8) = codeMat 128 := by
      unfold actionA; rw [step113_262s17_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 8 * (codeMat 142 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 416 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 416 (by decide)
    have hact : actionA (codeMat 161) (codeMat 354) (codeMat 416) = codeMat 96 := by
      unfold actionA; rw [step113_262s17_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 416 * (codeMat 142 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 64 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 64 (by decide)
    have hact : actionA (codeMat 161) (codeMat 354) (codeMat 64) = codeMat 16 := by
      unfold actionA; rw [step113_262s17_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 64 * (codeMat 142 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 256 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 161) (codeMat 354) (codeMat 256) = codeMat 8 := by
      unfold actionA; rw [step113_262s17_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 256 * (codeMat 142 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 6 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 6 (by decide)
    have hact : actionA (codeMat 161) (codeMat 354) (codeMat 6) = codeMat 4 := by
      unfold actionA; rw [step113_262s17_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 6 * (codeMat 142 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 1 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 354) (codeMat 1) = codeMat 2 := by
      unfold actionA; rw [step113_262s17_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 142 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 4 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 4 (by decide)
    have hact : actionA (codeMat 161) (codeMat 354) (codeMat 4) = codeMat 1 := by
      unfold actionA; rw [step113_262s17_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 4 * (codeMat 142 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row17_qr : QuotientRankAtLeast step113_262ActualSource17 6 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 354 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 354) flatW_2) 6 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 354) hP hQ flatW_2 6 QiushiMatmul.flatSeed_2
  exact quotientRankAtLeast_mono step113_262s17_source_le hAct

-- Source 18: row 323, orbit 2, lb 6, cap 10
def step113_262ActualSource18 : Submodule F2 Mat3 := spanCodes [256, 128, 80, 48, 8, 4, 2, 1]

theorem step113_262_row18_W_le_source : o262W ≤ step113_262ActualSource18 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource18
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 80, 48, 8, 4, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 80, 48, 8, 4, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 80, 48, 8, 4, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 80, 48, 8, 4, 2, 1] 1 (by decide)

private theorem step113_262s18_QtInv :
    (codeMat 114 : Mat3).transpose⁻¹ = (codeMat 204 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 114 : Mat3).transpose * (codeMat 204 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s18_source_le :
    step113_262ActualSource18 ≤ actionW (codeMat 161) (codeMat 114) flatW_2 := by
  apply step113_262_spanCodes_le_of_gens [256, 128, 80, 48, 8, 4, 2, 1]
    (actionW (codeMat 161) (codeMat 114) flatW_2)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 16 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 16 (by decide)
    have hact : actionA (codeMat 161) (codeMat 114) (codeMat 16) = codeMat 256 := by
      unfold actionA; rw [step113_262s18_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 16 * (codeMat 204 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 24 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 24 (by decide)
    have hact : actionA (codeMat 161) (codeMat 114) (codeMat 24) = codeMat 128 := by
      unfold actionA; rw [step113_262s18_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 24 * (codeMat 204 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 224 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 224 (by decide)
    have hact : actionA (codeMat 161) (codeMat 114) (codeMat 224) = codeMat 80 := by
      unfold actionA; rw [step113_262s18_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 224 * (codeMat 204 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 64 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 64 (by decide)
    have hact : actionA (codeMat 161) (codeMat 114) (codeMat 64) = codeMat 48 := by
      unfold actionA; rw [step113_262s18_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 64 * (codeMat 204 : Mat3).transpose = codeMat 48
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 256 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 161) (codeMat 114) (codeMat 256) = codeMat 8 := by
      unfold actionA; rw [step113_262s18_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 256 * (codeMat 204 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 114) (codeMat 2) = codeMat 4 := by
      unfold actionA; rw [step113_262s18_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 204 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 3 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 161) (codeMat 114) (codeMat 3) = codeMat 2 := by
      unfold actionA; rw [step113_262s18_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 3 * (codeMat 204 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 4 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 4 (by decide)
    have hact : actionA (codeMat 161) (codeMat 114) (codeMat 4) = codeMat 1 := by
      unfold actionA; rw [step113_262s18_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 4 * (codeMat 204 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row18_qr : QuotientRankAtLeast step113_262ActualSource18 6 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 114 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 114) flatW_2) 6 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 114) hP hQ flatW_2 6 QiushiMatmul.flatSeed_2
  exact quotientRankAtLeast_mono step113_262s18_source_le hAct

-- Source 19: row 328, orbit 2, lb 6, cap 10
def step113_262ActualSource19 : Submodule F2 Mat3 := spanCodes [272, 128, 80, 48, 8, 4, 2, 1]

theorem step113_262_row19_W_le_source : o262W ≤ step113_262ActualSource19 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource19
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 128, 80, 48, 8, 4, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 128, 80, 48, 8, 4, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 128, 80, 48, 8, 4, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 128, 80, 48, 8, 4, 2, 1] 1 (by decide)

private theorem step113_262s19_QtInv :
    (codeMat 369 : Mat3).transpose⁻¹ = (codeMat 377 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 369 : Mat3).transpose * (codeMat 377 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s19_source_le :
    step113_262ActualSource19 ≤ actionW (codeMat 161) (codeMat 369) flatW_2 := by
  apply step113_262_spanCodes_le_of_gens [272, 128, 80, 48, 8, 4, 2, 1]
    (actionW (codeMat 161) (codeMat 369) flatW_2)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 176 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 176 (by decide)
    have hact : actionA (codeMat 161) (codeMat 369) (codeMat 176) = codeMat 272 := by
      unfold actionA; rw [step113_262s19_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 176 * (codeMat 377 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 16 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 16 (by decide)
    have hact : actionA (codeMat 161) (codeMat 369) (codeMat 16) = codeMat 128 := by
      unfold actionA; rw [step113_262s19_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 16 * (codeMat 377 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 168 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 168 (by decide)
    have hact : actionA (codeMat 161) (codeMat 369) (codeMat 168) = codeMat 80 := by
      unfold actionA; rw [step113_262s19_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 168 * (codeMat 377 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 161) (codeMat 369) (codeMat 256) = codeMat 48 := by
      unfold actionA; rw [step113_262s19_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 256 * (codeMat 377 : Mat3).transpose = codeMat 48
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 320 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 320 (by decide)
    have hact : actionA (codeMat 161) (codeMat 369) (codeMat 320) = codeMat 8 := by
      unfold actionA; rw [step113_262s19_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 320 * (codeMat 377 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 6 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 6 (by decide)
    have hact : actionA (codeMat 161) (codeMat 369) (codeMat 6) = codeMat 4 := by
      unfold actionA; rw [step113_262s19_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 6 * (codeMat 377 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 369) (codeMat 2) = codeMat 2 := by
      unfold actionA; rw [step113_262s19_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 377 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 5 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 5 (by decide)
    have hact : actionA (codeMat 161) (codeMat 369) (codeMat 5) = codeMat 1 := by
      unfold actionA; rw [step113_262s19_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 5 * (codeMat 377 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row19_qr : QuotientRankAtLeast step113_262ActualSource19 6 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 369 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 369) flatW_2) 6 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 369) hP hQ flatW_2 6 QiushiMatmul.flatSeed_2
  exact quotientRankAtLeast_mono step113_262s19_source_le hAct

-- Source 20: row 329, orbit 2, lb 6, cap 10
def step113_262ActualSource20 : Submodule F2 Mat3 := spanCodes [256, 128, 80, 32, 8, 4, 2, 1]

theorem step113_262_row20_W_le_source : o262W ≤ step113_262ActualSource20 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource20
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 80, 32, 8, 4, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 80, 32, 8, 4, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 80, 32, 8, 4, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 80, 32, 8, 4, 2, 1] 1 (by decide)

private theorem step113_262s20_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s20_source_le :
    step113_262ActualSource20 ≤ actionW (codeMat 161) (codeMat 84) flatW_2 := by
  apply step113_262_spanCodes_le_of_gens [256, 128, 80, 32, 8, 4, 2, 1]
    (actionW (codeMat 161) (codeMat 84) flatW_2)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 8 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 161) (codeMat 84) (codeMat 8) = codeMat 256 := by
      unfold actionA; rw [step113_262s20_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 8 * (codeMat 84 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 16 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 16 (by decide)
    have hact : actionA (codeMat 161) (codeMat 84) (codeMat 16) = codeMat 128 := by
      unfold actionA; rw [step113_262s20_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 16 * (codeMat 84 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 160 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 84) (codeMat 160) = codeMat 80 := by
      unfold actionA; rw [step113_262s20_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * (codeMat 84 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 64 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 64 (by decide)
    have hact : actionA (codeMat 161) (codeMat 84) (codeMat 64) = codeMat 32 := by
      unfold actionA; rw [step113_262s20_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 64 * (codeMat 84 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 256 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 161) (codeMat 84) (codeMat 256) = codeMat 8 := by
      unfold actionA; rw [step113_262s20_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 256 * (codeMat 84 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 84) (codeMat 1) = codeMat 4 := by
      unfold actionA; rw [step113_262s20_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 84 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 84) (codeMat 2) = codeMat 2 := by
      unfold actionA; rw [step113_262s20_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 84 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 4 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 4 (by decide)
    have hact : actionA (codeMat 161) (codeMat 84) (codeMat 4) = codeMat 1 := by
      unfold actionA; rw [step113_262s20_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 4 * (codeMat 84 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row20_qr : QuotientRankAtLeast step113_262ActualSource20 6 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 84) flatW_2) 6 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 84) hP hQ flatW_2 6 QiushiMatmul.flatSeed_2
  exact quotientRankAtLeast_mono step113_262s20_source_le hAct

-- Source 21: row 333, orbit 3, lb 9, cap 7
def step113_262ActualSource21 : Submodule F2 Mat3 := spanCodes [260, 132, 68, 32, 16, 12, 2, 1]

theorem step113_262_row21_W_le_source : o262W ≤ step113_262ActualSource21 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource21
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 132, 68, 32, 16, 12, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 132, 68, 32, 16, 12, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 132, 68, 32, 16, 12, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 132, 68, 32, 16, 12, 2, 1] 1 (by decide)

private theorem step113_262s21_QtInv :
    (codeMat 460 : Mat3).transpose⁻¹ = (codeMat 122 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 460 : Mat3).transpose * (codeMat 122 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s21_source_le :
    step113_262ActualSource21 ≤ actionW (codeMat 84) (codeMat 460) flatW_3 := by
  apply step113_262_spanCodes_le_of_gens [260, 132, 68, 32, 16, 12, 2, 1]
    (actionW (codeMat 84) (codeMat 460) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 325 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 325 (by decide)
    have hact : actionA (codeMat 84) (codeMat 460) (codeMat 325) = codeMat 260 := by
      unfold actionA; rw [step113_262s21_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 325 * (codeMat 122 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 324 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 324 (by decide)
    have hact : actionA (codeMat 84) (codeMat 460) (codeMat 324) = codeMat 132 := by
      unfold actionA; rw [step113_262s21_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 324 * (codeMat 122 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 326 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 326 (by decide)
    have hact : actionA (codeMat 84) (codeMat 460) (codeMat 326) = codeMat 68 := by
      unfold actionA; rw [step113_262s21_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 326 * (codeMat 122 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 40 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 84) (codeMat 460) (codeMat 40) = codeMat 32 := by
      unfold actionA; rw [step113_262s21_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 40 * (codeMat 122 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 32 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 84) (codeMat 460) (codeMat 32) = codeMat 16 := by
      unfold actionA; rw [step113_262s21_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 32 * (codeMat 122 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 368 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 368 (by decide)
    have hact : actionA (codeMat 84) (codeMat 460) (codeMat 368) = codeMat 12 := by
      unfold actionA; rw [step113_262s21_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 368 * (codeMat 122 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 460) (codeMat 256) = codeMat 2 := by
      unfold actionA; rw [step113_262s21_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 122 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 460) (codeMat 384) = codeMat 1 := by
      unfold actionA; rw [step113_262s21_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 122 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row21_qr : QuotientRankAtLeast step113_262ActualSource21 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 460 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 460) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 460) hP hQ flatW_3 9 QiushiMatmul.flatSeed_3
  exact quotientRankAtLeast_mono step113_262s21_source_le hAct

-- Source 22: row 335, orbit 3, lb 9, cap 7
def step113_262ActualSource22 : Submodule F2 Mat3 := spanCodes [256, 132, 68, 36, 16, 12, 2, 1]

theorem step113_262_row22_W_le_source : o262W ≤ step113_262ActualSource22 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource22
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 68, 36, 16, 12, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 68, 36, 16, 12, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 68, 36, 16, 12, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 68, 36, 16, 12, 2, 1] 1 (by decide)

private theorem step113_262s22_QtInv :
    (codeMat 236 : Mat3).transpose⁻¹ = (codeMat 123 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 236 : Mat3).transpose * (codeMat 123 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s22_source_le :
    step113_262ActualSource22 ≤ actionW (codeMat 84) (codeMat 236) flatW_3 := by
  apply step113_262_spanCodes_le_of_gens [256, 132, 68, 36, 16, 12, 2, 1]
    (actionW (codeMat 84) (codeMat 236) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 3 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 84) (codeMat 236) (codeMat 3) = codeMat 256 := by
      unfold actionA; rw [step113_262s22_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 3 * (codeMat 123 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 196 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 196 (by decide)
    have hact : actionA (codeMat 84) (codeMat 236) (codeMat 196) = codeMat 132 := by
      unfold actionA; rw [step113_262s22_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 196 * (codeMat 123 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 198 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 198 (by decide)
    have hact : actionA (codeMat 84) (codeMat 236) (codeMat 198) = codeMat 68 := by
      unfold actionA; rw [step113_262s22_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 198 * (codeMat 123 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 216 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 216 (by decide)
    have hact : actionA (codeMat 84) (codeMat 236) (codeMat 216) = codeMat 36 := by
      unfold actionA; rw [step113_262s22_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 216 * (codeMat 123 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 32 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 84) (codeMat 236) (codeMat 32) = codeMat 16 := by
      unfold actionA; rw [step113_262s22_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 32 * (codeMat 123 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 240 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 240 (by decide)
    have hact : actionA (codeMat 84) (codeMat 236) (codeMat 240) = codeMat 12 := by
      unfold actionA; rw [step113_262s22_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 240 * (codeMat 123 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 236) (codeMat 256) = codeMat 2 := by
      unfold actionA; rw [step113_262s22_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 123 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 236) (codeMat 384) = codeMat 1 := by
      unfold actionA; rw [step113_262s22_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 123 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row22_qr : QuotientRankAtLeast step113_262ActualSource22 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 236 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 236) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 236) hP hQ flatW_3 9 QiushiMatmul.flatSeed_3
  exact quotientRankAtLeast_mono step113_262s22_source_le hAct

-- Source 23: row 1, orbit 96, lb 16, cap 0
def step113_262ActualSource23 : Submodule F2 Mat3 := spanCodes [132, 16, 12, 2, 1]

theorem step113_262_row23_W_le_source : o262W ≤ step113_262ActualSource23 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource23
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [132, 16, 12, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [132, 16, 12, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [132, 16, 12, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [132, 16, 12, 2, 1] 1 (by decide)

private theorem step113_262s23_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s23_source_le :
    step113_262ActualSource23 ≤ actionW (codeMat 273) (codeMat 266) o96W_wc := by
  apply step113_262_spanCodes_le_of_gens [132, 16, 12, 2, 1]
    (actionW (codeMat 273) (codeMat 266) o96W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 68 ∈ o96W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [68, 20, 8, 2, 1] 68 (by decide)
    have hact : actionA (codeMat 273) (codeMat 266) (codeMat 68) = codeMat 132 := by
      unfold actionA; rw [step113_262s23_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 68 * (codeMat 266 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 8 ∈ o96W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [68, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 266) (codeMat 8) = codeMat 16 := by
      unfold actionA; rw [step113_262s23_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 266 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 20 ∈ o96W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [68, 20, 8, 2, 1] 20 (by decide)
    have hact : actionA (codeMat 273) (codeMat 266) (codeMat 20) = codeMat 12 := by
      unfold actionA; rw [step113_262s23_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 20 * (codeMat 266 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o96W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [68, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 266) (codeMat 1) = codeMat 2 := by
      unfold actionA; rw [step113_262s23_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o96W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [68, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 266) (codeMat 2) = codeMat 1 := by
      unfold actionA; rw [step113_262s23_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row23_qr : QuotientRankAtLeast step113_262ActualSource23 16 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 266) o96W_wc) 16 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 266) hP hQ o96W_wc 16 QiushiMatmul.step109_orbit96_lb16_wc
  exact quotientRankAtLeast_mono step113_262s23_source_le hAct

-- Source 24: row 50, orbit 31, lb 15, cap 1
def step113_262ActualSource24 : Submodule F2 Mat3 := spanCodes [132, 64, 20, 12, 2, 1]

theorem step113_262_row24_W_le_source : o262W ≤ step113_262ActualSource24 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource24
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [132, 64, 20, 12, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [132, 64, 20, 12, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [132, 64, 20, 12, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [132, 64, 20, 12, 2, 1] 1 (by decide)

private theorem step113_262s24_QtInv :
    (codeMat 401 : Mat3).transpose⁻¹ = (codeMat 401 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 401 : Mat3).transpose * (codeMat 401 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s24_source_le :
    step113_262ActualSource24 ≤ transposeW (actionW (codeMat 266) (codeMat 401) orbit31W) := by
  apply step113_262_spanCodes_le_of_gens [132, 64, 20, 12, 2, 1]
    (transposeW (actionW (codeMat 266) (codeMat 401) orbit31W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 68 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 68 (by decide)
    have hact : actionA (codeMat 266) (codeMat 401) (codeMat 68) = codeMat 96 := by
      unfold actionA; rw [step113_262s24_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 68 * (codeMat 401 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 96 ∈ actionW (codeMat 266) (codeMat 401) orbit31W :=
      step113_262_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 96 : Mat3).transpose = codeMat 132 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h1
    have hw : codeMat 32 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 32 (by decide)
    have hact : actionA (codeMat 266) (codeMat 401) (codeMat 32) = codeMat 4 := by
      unfold actionA; rw [step113_262s24_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 401 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 4 ∈ actionW (codeMat 266) (codeMat 401) orbit31W :=
      step113_262_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 4 : Mat3).transpose = codeMat 64 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h2
    have hw : codeMat 70 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 70 (by decide)
    have hact : actionA (codeMat 266) (codeMat 401) (codeMat 70) = codeMat 80 := by
      unfold actionA; rw [step113_262s24_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 70 * (codeMat 401 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 80 ∈ actionW (codeMat 266) (codeMat 401) orbit31W :=
      step113_262_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 80 : Mat3).transpose = codeMat 20 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h3
    have hw : codeMat 112 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 112 (by decide)
    have hact : actionA (codeMat 266) (codeMat 401) (codeMat 112) = codeMat 66 := by
      unfold actionA; rw [step113_262s24_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 112 * (codeMat 401 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 66 ∈ actionW (codeMat 266) (codeMat 401) orbit31W :=
      step113_262_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 66 : Mat3).transpose = codeMat 12 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h4
    have hw : codeMat 1 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 401) (codeMat 1) = codeMat 8 := by
      unfold actionA; rw [step113_262s24_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 401 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 8 ∈ actionW (codeMat 266) (codeMat 401) orbit31W :=
      step113_262_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 8 : Mat3).transpose = codeMat 2 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h5
    have hw : codeMat 8 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 401) (codeMat 8) = codeMat 1 := by
      unfold actionA; rw [step113_262s24_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 401 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 1 ∈ actionW (codeMat 266) (codeMat 401) orbit31W :=
      step113_262_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 1 : Mat3).transpose = codeMat 1 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_transposeW_of_witness hmA htrans

theorem step113_262_row24_qr : QuotientRankAtLeast step113_262ActualSource24 15 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 401) orbit31W) 15 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 401) hP hQ orbit31W 15 QiushiMatmul.orbit31_lb15
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 266) (codeMat 401) orbit31W)) 15 :=
    quotientRankAtLeast_transpose hAct
  exact quotientRankAtLeast_mono step113_262s24_source_le hT

-- Source 25: row 51, orbit 31, lb 15, cap 1
def step113_262ActualSource25 : Submodule F2 Mat3 := spanCodes [132, 68, 16, 12, 2, 1]

theorem step113_262_row25_W_le_source : o262W ≤ step113_262ActualSource25 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource25
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [132, 68, 16, 12, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [132, 68, 16, 12, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [132, 68, 16, 12, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [132, 68, 16, 12, 2, 1] 1 (by decide)

private theorem step113_262s25_QtInv :
    (codeMat 305 : Mat3).transpose⁻¹ = (codeMat 305 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 305 : Mat3).transpose * (codeMat 305 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s25_source_le :
    step113_262ActualSource25 ≤ transposeW (actionW (codeMat 266) (codeMat 305) orbit31W) := by
  apply step113_262_spanCodes_le_of_gens [132, 68, 16, 12, 2, 1]
    (transposeW (actionW (codeMat 266) (codeMat 305) orbit31W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 70 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 70 (by decide)
    have hact : actionA (codeMat 266) (codeMat 305) (codeMat 70) = codeMat 96 := by
      unfold actionA; rw [step113_262s25_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 70 * (codeMat 305 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 96 ∈ actionW (codeMat 266) (codeMat 305) orbit31W :=
      step113_262_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 96 : Mat3).transpose = codeMat 132 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h1
    have hw : codeMat 112 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 112 (by decide)
    have hact : actionA (codeMat 266) (codeMat 305) (codeMat 112) = codeMat 68 := by
      unfold actionA; rw [step113_262s25_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 112 * (codeMat 305 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 68 ∈ actionW (codeMat 266) (codeMat 305) orbit31W :=
      step113_262_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 68 : Mat3).transpose = codeMat 68 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h2
    have hw : codeMat 2 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 305) (codeMat 2) = codeMat 16 := by
      unfold actionA; rw [step113_262s25_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 305 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 16 ∈ actionW (codeMat 266) (codeMat 305) orbit31W :=
      step113_262_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 16 : Mat3).transpose = codeMat 16 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h3
    have hw : codeMat 80 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 80 (by decide)
    have hact : actionA (codeMat 266) (codeMat 305) (codeMat 80) = codeMat 66 := by
      unfold actionA; rw [step113_262s25_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 80 * (codeMat 305 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 66 ∈ actionW (codeMat 266) (codeMat 305) orbit31W :=
      step113_262_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 66 : Mat3).transpose = codeMat 12 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h4
    have hw : codeMat 1 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 305) (codeMat 1) = codeMat 8 := by
      unfold actionA; rw [step113_262s25_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 305 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 8 ∈ actionW (codeMat 266) (codeMat 305) orbit31W :=
      step113_262_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 8 : Mat3).transpose = codeMat 2 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h5
    have hw : codeMat 8 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 305) (codeMat 8) = codeMat 1 := by
      unfold actionA; rw [step113_262s25_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 305 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 1 ∈ actionW (codeMat 266) (codeMat 305) orbit31W :=
      step113_262_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 1 : Mat3).transpose = codeMat 1 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_transposeW_of_witness hmA htrans

theorem step113_262_row25_qr : QuotientRankAtLeast step113_262ActualSource25 15 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 305) orbit31W) 15 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 305) hP hQ orbit31W 15 QiushiMatmul.orbit31_lb15
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 266) (codeMat 305) orbit31W)) 15 :=
    quotientRankAtLeast_transpose hAct
  exact quotientRankAtLeast_mono step113_262s25_source_le hT

-- Source 26: row 83, orbit 35, lb 15, cap 1
def step113_262ActualSource26 : Submodule F2 Mat3 := spanCodes [308, 132, 80, 12, 2, 1]

theorem step113_262_row26_W_le_source : o262W ≤ step113_262ActualSource26 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource26
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [308, 132, 80, 12, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [308, 132, 80, 12, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [308, 132, 80, 12, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [308, 132, 80, 12, 2, 1] 1 (by decide)

private theorem step113_262s26_QtInv :
    (codeMat 417 : Mat3).transpose⁻¹ = (codeMat 177 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 417 : Mat3).transpose * (codeMat 177 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s26_source_le :
    step113_262ActualSource26 ≤ transposeW (actionW (codeMat 331) (codeMat 417) orbit35W) := by
  apply step113_262_spanCodes_le_of_gens [308, 132, 80, 12, 2, 1]
    (transposeW (actionW (codeMat 331) (codeMat 417) orbit35W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 252 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 252 (by decide)
    have hact : actionA (codeMat 331) (codeMat 417) (codeMat 252) = codeMat 464 := by
      unfold actionA; rw [step113_262s26_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 252 * (codeMat 177 : Mat3).transpose = codeMat 464
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 464 ∈ actionW (codeMat 331) (codeMat 417) orbit35W :=
      step113_262_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 464 : Mat3).transpose = codeMat 308 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h1
    have hw : codeMat 126 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 126 (by decide)
    have hact : actionA (codeMat 331) (codeMat 417) (codeMat 126) = codeMat 96 := by
      unfold actionA; rw [step113_262s26_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 126 * (codeMat 177 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 96 ∈ actionW (codeMat 331) (codeMat 417) orbit35W :=
      step113_262_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 96 : Mat3).transpose = codeMat 132 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h2
    have hw : codeMat 20 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 20 (by decide)
    have hact : actionA (codeMat 331) (codeMat 417) (codeMat 20) = codeMat 20 := by
      unfold actionA; rw [step113_262s26_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 20 * (codeMat 177 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 20 ∈ actionW (codeMat 331) (codeMat 417) orbit35W :=
      step113_262_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 20 : Mat3).transpose = codeMat 80 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h3
    have hw : codeMat 104 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 104 (by decide)
    have hact : actionA (codeMat 331) (codeMat 417) (codeMat 104) = codeMat 66 := by
      unfold actionA; rw [step113_262s26_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 104 * (codeMat 177 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 66 ∈ actionW (codeMat 331) (codeMat 417) orbit35W :=
      step113_262_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 66 : Mat3).transpose = codeMat 12 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h4
    have hw : codeMat 9 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 9 (by decide)
    have hact : actionA (codeMat 331) (codeMat 417) (codeMat 9) = codeMat 8 := by
      unfold actionA; rw [step113_262s26_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 9 * (codeMat 177 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 8 ∈ actionW (codeMat 331) (codeMat 417) orbit35W :=
      step113_262_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 8 : Mat3).transpose = codeMat 2 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h5
    have hw : codeMat 8 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 8 (by decide)
    have hact : actionA (codeMat 331) (codeMat 417) (codeMat 8) = codeMat 1 := by
      unfold actionA; rw [step113_262s26_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 8 * (codeMat 177 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 1 ∈ actionW (codeMat 331) (codeMat 417) orbit35W :=
      step113_262_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 1 : Mat3).transpose = codeMat 1 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_transposeW_of_witness hmA htrans

theorem step113_262_row26_qr : QuotientRankAtLeast step113_262ActualSource26 15 := by
  have hP : Invertible (codeMat 331 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 331) (codeMat 417) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 331) (codeMat 417) hP hQ orbit35W 15 QiushiMatmul.orbit35_lb15
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 331) (codeMat 417) orbit35W)) 15 :=
    quotientRankAtLeast_transpose hAct
  exact quotientRankAtLeast_mono step113_262s26_source_le hT

-- Source 27: row 184, orbit 7, lb 9, cap 7
def step113_262ActualSource27 : Submodule F2 Mat3 := spanCodes [288, 128, 96, 8, 4, 2, 1]

theorem step113_262_row27_W_le_source : o262W ≤ step113_262ActualSource27 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource27
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 128, 96, 8, 4, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 128, 96, 8, 4, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 128, 96, 8, 4, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 128, 96, 8, 4, 2, 1] 1 (by decide)

private theorem step113_262s27_QtInv :
    (codeMat 340 : Mat3).transpose⁻¹ = (codeMat 85 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 340 : Mat3).transpose * (codeMat 85 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s27_source_le :
    step113_262ActualSource27 ≤ actionW (codeMat 161) (codeMat 340) flatW_7 := by
  apply step113_262_spanCodes_le_of_gens [288, 128, 96, 8, 4, 2, 1]
    (actionW (codeMat 161) (codeMat 340) flatW_7)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 360 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 360 (by decide)
    have hact : actionA (codeMat 161) (codeMat 340) (codeMat 360) = codeMat 288 := by
      unfold actionA; rw [step113_262s27_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 360 * (codeMat 85 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 16 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 16 (by decide)
    have hact : actionA (codeMat 161) (codeMat 340) (codeMat 16) = codeMat 128 := by
      unfold actionA; rw [step113_262s27_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 16 * (codeMat 85 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 352 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 352 (by decide)
    have hact : actionA (codeMat 161) (codeMat 340) (codeMat 352) = codeMat 96 := by
      unfold actionA; rw [step113_262s27_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 352 * (codeMat 85 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 161) (codeMat 340) (codeMat 256) = codeMat 8 := by
      unfold actionA; rw [step113_262s27_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 256 * (codeMat 85 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 5 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 5 (by decide)
    have hact : actionA (codeMat 161) (codeMat 340) (codeMat 5) = codeMat 4 := by
      unfold actionA; rw [step113_262s27_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 5 * (codeMat 85 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 340) (codeMat 2) = codeMat 2 := by
      unfold actionA; rw [step113_262s27_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 85 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 4 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 4 (by decide)
    have hact : actionA (codeMat 161) (codeMat 340) (codeMat 4) = codeMat 1 := by
      unfold actionA; rw [step113_262s27_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 4 * (codeMat 85 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row27_qr : QuotientRankAtLeast step113_262ActualSource27 9 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 340 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 340) flatW_7) 9 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 340) hP hQ flatW_7 9 QiushiMatmul.flatSeed_7
  exact quotientRankAtLeast_mono step113_262s27_source_le hAct

-- Source 28: row 189, orbit 7, lb 9, cap 7
def step113_262ActualSource28 : Submodule F2 Mat3 := spanCodes [256, 128, 96, 8, 4, 2, 1]

theorem step113_262_row28_W_le_source : o262W ≤ step113_262ActualSource28 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource28
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 96, 8, 4, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 96, 8, 4, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 96, 8, 4, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 96, 8, 4, 2, 1] 1 (by decide)

private theorem step113_262s28_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s28_source_le :
    step113_262ActualSource28 ≤ actionW (codeMat 161) (codeMat 84) flatW_7 := by
  apply step113_262_spanCodes_le_of_gens [256, 128, 96, 8, 4, 2, 1]
    (actionW (codeMat 161) (codeMat 84) flatW_7)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 8 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 161) (codeMat 84) (codeMat 8) = codeMat 256 := by
      unfold actionA; rw [step113_262s28_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 8 * (codeMat 84 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 16 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 16 (by decide)
    have hact : actionA (codeMat 161) (codeMat 84) (codeMat 16) = codeMat 128 := by
      unfold actionA; rw [step113_262s28_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 16 * (codeMat 84 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 96 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 96 (by decide)
    have hact : actionA (codeMat 161) (codeMat 84) (codeMat 96) = codeMat 96 := by
      unfold actionA; rw [step113_262s28_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 96 * (codeMat 84 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 161) (codeMat 84) (codeMat 256) = codeMat 8 := by
      unfold actionA; rw [step113_262s28_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 256 * (codeMat 84 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 84) (codeMat 1) = codeMat 4 := by
      unfold actionA; rw [step113_262s28_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 84 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 84) (codeMat 2) = codeMat 2 := by
      unfold actionA; rw [step113_262s28_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 84 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 4 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 4 (by decide)
    have hact : actionA (codeMat 161) (codeMat 84) (codeMat 4) = codeMat 1 := by
      unfold actionA; rw [step113_262s28_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 4 * (codeMat 84 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row28_qr : QuotientRankAtLeast step113_262ActualSource28 9 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 84) flatW_7) 9 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 84) hP hQ flatW_7 9 QiushiMatmul.flatSeed_7
  exact quotientRankAtLeast_mono step113_262s28_source_le hAct

-- Source 29: row 215, orbit 11, lb 12, cap 4
def step113_262ActualSource29 : Submodule F2 Mat3 := spanCodes [256, 132, 64, 32, 12, 2, 1]

theorem step113_262_row29_W_le_source : o262W ≤ step113_262ActualSource29 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource29
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 32, 12, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 32, 12, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 32, 12, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 32, 12, 2, 1] 1 (by decide)

private theorem step113_262s29_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s29_source_le :
    step113_262ActualSource29 ≤ actionW (codeMat 140) (codeMat 161) orbit11W := by
  apply step113_262_spanCodes_le_of_gens [256, 132, 64, 32, 12, 2, 1]
    (actionW (codeMat 140) (codeMat 161) orbit11W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 2 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 2 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 2) = codeMat 256 := by
      unfold actionA; rw [step113_262s29_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 2 * (codeMat 161 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 20 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 20 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 20) = codeMat 132 := by
      unfold actionA; rw [step113_262s29_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 20 * (codeMat 161 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 1 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 1) = codeMat 64 := by
      unfold actionA; rw [step113_262s29_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 128 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 128 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 128) = codeMat 32 := by
      unfold actionA; rw [step113_262s29_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 128 * (codeMat 161 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 80 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 80 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 80) = codeMat 12 := by
      unfold actionA; rw [step113_262s29_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 80 * (codeMat 161 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 32 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 32) = codeMat 2 := by
      unfold actionA; rw [step113_262s29_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 32 * (codeMat 161 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 8 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 8) = codeMat 1 := by
      unfold actionA; rw [step113_262s29_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 8 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row29_qr : QuotientRankAtLeast step113_262ActualSource29 12 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 161) orbit11W) 12 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 161) hP hQ orbit11W 12 QiushiMatmul.orbit11_lb12
  exact quotientRankAtLeast_mono step113_262s29_source_le hAct

-- Source 30: row 216, orbit 11, lb 12, cap 4
def step113_262ActualSource30 : Submodule F2 Mat3 := spanCodes [260, 132, 64, 36, 12, 2, 1]

theorem step113_262_row30_W_le_source : o262W ≤ step113_262ActualSource30 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource30
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 132, 64, 36, 12, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 132, 64, 36, 12, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 132, 64, 36, 12, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 132, 64, 36, 12, 2, 1] 1 (by decide)

private theorem step113_262s30_QtInv :
    (codeMat 165 : Mat3).transpose⁻¹ = (codeMat 163 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 165 : Mat3).transpose * (codeMat 163 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s30_source_le :
    step113_262ActualSource30 ≤ actionW (codeMat 141) (codeMat 165) orbit11W := by
  apply step113_262_spanCodes_le_of_gens [260, 132, 64, 36, 12, 2, 1]
    (actionW (codeMat 141) (codeMat 165) orbit11W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 3 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 3 (by decide)
    have hact : actionA (codeMat 141) (codeMat 165) (codeMat 3) = codeMat 260 := by
      unfold actionA; rw [step113_262s30_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 3 * (codeMat 163 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 60 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 60 (by decide)
    have hact : actionA (codeMat 141) (codeMat 165) (codeMat 60) = codeMat 132 := by
      unfold actionA; rw [step113_262s30_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 60 * (codeMat 163 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 9 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 9 (by decide)
    have hact : actionA (codeMat 141) (codeMat 165) (codeMat 9) = codeMat 64 := by
      unfold actionA; rw [step113_262s30_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 9 * (codeMat 163 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 216 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 216 (by decide)
    have hact : actionA (codeMat 141) (codeMat 165) (codeMat 216) = codeMat 36 := by
      unfold actionA; rw [step113_262s30_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 216 * (codeMat 163 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 88 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 88 (by decide)
    have hact : actionA (codeMat 141) (codeMat 165) (codeMat 88) = codeMat 12 := by
      unfold actionA; rw [step113_262s30_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 88 * (codeMat 163 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 32 (by decide)
    have hact : actionA (codeMat 141) (codeMat 165) (codeMat 32) = codeMat 2 := by
      unfold actionA; rw [step113_262s30_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 32 * (codeMat 163 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 8 (by decide)
    have hact : actionA (codeMat 141) (codeMat 165) (codeMat 8) = codeMat 1 := by
      unfold actionA; rw [step113_262s30_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 8 * (codeMat 163 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row30_qr : QuotientRankAtLeast step113_262ActualSource30 12 := by
  have hP : Invertible (codeMat 141 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 165 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 141) (codeMat 165) orbit11W) 12 :=
    @quotientRankAtLeast_action (codeMat 141) (codeMat 165) hP hQ orbit11W 12 QiushiMatmul.orbit11_lb12
  exact quotientRankAtLeast_mono step113_262s30_source_le hAct

-- Source 31: row 321, orbit 2, lb 6, cap 10
def step113_262ActualSource31 : Submodule F2 Mat3 := spanCodes [272, 128, 80, 32, 8, 4, 2, 1]

theorem step113_262_row31_W_le_source : o262W ≤ step113_262ActualSource31 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource31
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 128, 80, 32, 8, 4, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 128, 80, 32, 8, 4, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 128, 80, 32, 8, 4, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 128, 80, 32, 8, 4, 2, 1] 1 (by decide)

private theorem step113_262s31_QtInv :
    (codeMat 337 : Mat3).transpose⁻¹ = (codeMat 337 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 337 : Mat3).transpose * (codeMat 337 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s31_source_le :
    step113_262ActualSource31 ≤ actionW (codeMat 161) (codeMat 337) flatW_2 := by
  apply step113_262_spanCodes_le_of_gens [272, 128, 80, 32, 8, 4, 2, 1]
    (actionW (codeMat 161) (codeMat 337) flatW_2)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 160 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 337) (codeMat 160) = codeMat 272 := by
      unfold actionA; rw [step113_262s31_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * (codeMat 337 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 16 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 16 (by decide)
    have hact : actionA (codeMat 161) (codeMat 337) (codeMat 16) = codeMat 128 := by
      unfold actionA; rw [step113_262s31_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 16 * (codeMat 337 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 168 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 168 (by decide)
    have hact : actionA (codeMat 161) (codeMat 337) (codeMat 168) = codeMat 80 := by
      unfold actionA; rw [step113_262s31_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 168 * (codeMat 337 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 161) (codeMat 337) (codeMat 256) = codeMat 32 := by
      unfold actionA; rw [step113_262s31_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 256 * (codeMat 337 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 320 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 320 (by decide)
    have hact : actionA (codeMat 161) (codeMat 337) (codeMat 320) = codeMat 8 := by
      unfold actionA; rw [step113_262s31_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 320 * (codeMat 337 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 4 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 4 (by decide)
    have hact : actionA (codeMat 161) (codeMat 337) (codeMat 4) = codeMat 4 := by
      unfold actionA; rw [step113_262s31_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 4 * (codeMat 337 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 337) (codeMat 2) = codeMat 2 := by
      unfold actionA; rw [step113_262s31_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 337 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 5 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 5 (by decide)
    have hact : actionA (codeMat 161) (codeMat 337) (codeMat 5) = codeMat 1 := by
      unfold actionA; rw [step113_262s31_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 5 * (codeMat 337 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row31_qr : QuotientRankAtLeast step113_262ActualSource31 6 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 337 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 337) flatW_2) 6 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 337) hP hQ flatW_2 6 QiushiMatmul.flatSeed_2
  exact quotientRankAtLeast_mono step113_262s31_source_le hAct

-- Source 32: row 322, orbit 2, lb 6, cap 10
def step113_262ActualSource32 : Submodule F2 Mat3 := spanCodes [272, 128, 64, 48, 8, 4, 2, 1]

theorem step113_262_row32_W_le_source : o262W ≤ step113_262ActualSource32 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource32
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 128, 64, 48, 8, 4, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 128, 64, 48, 8, 4, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 128, 64, 48, 8, 4, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 128, 64, 48, 8, 4, 2, 1] 1 (by decide)

private theorem step113_262s32_QtInv :
    (codeMat 305 : Mat3).transpose⁻¹ = (codeMat 305 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 305 : Mat3).transpose * (codeMat 305 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s32_source_le :
    step113_262ActualSource32 ≤ actionW (codeMat 161) (codeMat 305) flatW_2 := by
  apply step113_262_spanCodes_le_of_gens [272, 128, 64, 48, 8, 4, 2, 1]
    (actionW (codeMat 161) (codeMat 305) flatW_2)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 176 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 176 (by decide)
    have hact : actionA (codeMat 161) (codeMat 305) (codeMat 176) = codeMat 272 := by
      unfold actionA; rw [step113_262s32_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 176 * (codeMat 305 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 16 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 16 (by decide)
    have hact : actionA (codeMat 161) (codeMat 305) (codeMat 16) = codeMat 128 := by
      unfold actionA; rw [step113_262s32_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 16 * (codeMat 305 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 161) (codeMat 305) (codeMat 8) = codeMat 64 := by
      unfold actionA; rw [step113_262s32_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 8 * (codeMat 305 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 161) (codeMat 305) (codeMat 256) = codeMat 48 := by
      unfold actionA; rw [step113_262s32_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 256 * (codeMat 305 : Mat3).transpose = codeMat 48
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 64 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 64 (by decide)
    have hact : actionA (codeMat 161) (codeMat 305) (codeMat 64) = codeMat 8 := by
      unfold actionA; rw [step113_262s32_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 64 * (codeMat 305 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 6 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 6 (by decide)
    have hact : actionA (codeMat 161) (codeMat 305) (codeMat 6) = codeMat 4 := by
      unfold actionA; rw [step113_262s32_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 6 * (codeMat 305 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 305) (codeMat 2) = codeMat 2 := by
      unfold actionA; rw [step113_262s32_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 305 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 1 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 305) (codeMat 1) = codeMat 1 := by
      unfold actionA; rw [step113_262s32_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 305 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row32_qr : QuotientRankAtLeast step113_262ActualSource32 6 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 305) flatW_2) 6 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 305) hP hQ flatW_2 6 QiushiMatmul.flatSeed_2
  exact quotientRankAtLeast_mono step113_262s32_source_le hAct

-- Source 33: row 336, orbit 3, lb 9, cap 7
def step113_262ActualSource33 : Submodule F2 Mat3 := spanCodes [260, 132, 64, 32, 20, 12, 2, 1]

theorem step113_262_row33_W_le_source : o262W ≤ step113_262ActualSource33 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource33
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 132, 64, 32, 20, 12, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 132, 64, 32, 20, 12, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 132, 64, 32, 20, 12, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 132, 64, 32, 20, 12, 2, 1] 1 (by decide)

private theorem step113_262s33_QtInv :
    (codeMat 412 : Mat3).transpose⁻¹ = (codeMat 111 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 412 : Mat3).transpose * (codeMat 111 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s33_source_le :
    step113_262ActualSource33 ≤ actionW (codeMat 84) (codeMat 412) flatW_3 := by
  apply step113_262_spanCodes_le_of_gens [260, 132, 64, 32, 20, 12, 2, 1]
    (actionW (codeMat 84) (codeMat 412) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 325 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 325 (by decide)
    have hact : actionA (codeMat 84) (codeMat 412) (codeMat 325) = codeMat 260 := by
      unfold actionA; rw [step113_262s33_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 325 * (codeMat 111 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 326 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 326 (by decide)
    have hact : actionA (codeMat 84) (codeMat 412) (codeMat 326) = codeMat 132 := by
      unfold actionA; rw [step113_262s33_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 326 * (codeMat 111 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 412) (codeMat 2) = codeMat 64 := by
      unfold actionA; rw [step113_262s33_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 111 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 40 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 84) (codeMat 412) (codeMat 40) = codeMat 32 := by
      unfold actionA; rw [step113_262s33_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 40 * (codeMat 111 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 368 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 368 (by decide)
    have hact : actionA (codeMat 84) (codeMat 412) (codeMat 368) = codeMat 20 := by
      unfold actionA; rw [step113_262s33_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 368 * (codeMat 111 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 336 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 336 (by decide)
    have hact : actionA (codeMat 84) (codeMat 412) (codeMat 336) = codeMat 12 := by
      unfold actionA; rw [step113_262s33_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 336 * (codeMat 111 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 412) (codeMat 384) = codeMat 2 := by
      unfold actionA; rw [step113_262s33_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 111 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 128 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 412) (codeMat 128) = codeMat 1 := by
      unfold actionA; rw [step113_262s33_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 111 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row33_qr : QuotientRankAtLeast step113_262ActualSource33 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 412 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 412) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 412) hP hQ flatW_3 9 QiushiMatmul.flatSeed_3
  exact quotientRankAtLeast_mono step113_262s33_source_le hAct

-- Source 34: row 337, orbit 3, lb 9, cap 7
def step113_262ActualSource34 : Submodule F2 Mat3 := spanCodes [256, 132, 64, 36, 20, 12, 2, 1]

theorem step113_262_row34_W_le_source : o262W ≤ step113_262ActualSource34 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource34
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 36, 20, 12, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 36, 20, 12, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 36, 20, 12, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 36, 20, 12, 2, 1] 1 (by decide)

private theorem step113_262s34_QtInv :
    (codeMat 188 : Mat3).transpose⁻¹ = (codeMat 103 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 188 : Mat3).transpose * (codeMat 103 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s34_source_le :
    step113_262ActualSource34 ≤ actionW (codeMat 84) (codeMat 188) flatW_3 := by
  apply step113_262_spanCodes_le_of_gens [256, 132, 64, 36, 20, 12, 2, 1]
    (actionW (codeMat 84) (codeMat 188) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 3 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 84) (codeMat 188) (codeMat 3) = codeMat 256 := by
      unfold actionA; rw [step113_262s34_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 3 * (codeMat 103 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 198 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 198 (by decide)
    have hact : actionA (codeMat 84) (codeMat 188) (codeMat 198) = codeMat 132 := by
      unfold actionA; rw [step113_262s34_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 198 * (codeMat 103 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 188) (codeMat 2) = codeMat 64 := by
      unfold actionA; rw [step113_262s34_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 103 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 216 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 216 (by decide)
    have hact : actionA (codeMat 84) (codeMat 188) (codeMat 216) = codeMat 36 := by
      unfold actionA; rw [step113_262s34_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 216 * (codeMat 103 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 240 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 240 (by decide)
    have hact : actionA (codeMat 84) (codeMat 188) (codeMat 240) = codeMat 20 := by
      unfold actionA; rw [step113_262s34_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 240 * (codeMat 103 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 208 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 208 (by decide)
    have hact : actionA (codeMat 84) (codeMat 188) (codeMat 208) = codeMat 12 := by
      unfold actionA; rw [step113_262s34_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 208 * (codeMat 103 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 188) (codeMat 384) = codeMat 2 := by
      unfold actionA; rw [step113_262s34_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 103 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 128 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 188) (codeMat 128) = codeMat 1 := by
      unfold actionA; rw [step113_262s34_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 103 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row34_qr : QuotientRankAtLeast step113_262ActualSource34 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 188 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 188) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 188) hP hQ flatW_3 9 QiushiMatmul.flatSeed_3
  exact quotientRankAtLeast_mono step113_262s34_source_le hAct

-- Source 35: row 85, orbit 35, lb 15, cap 1
def step113_262ActualSource35 : Submodule F2 Mat3 := spanCodes [292, 132, 80, 12, 2, 1]

theorem step113_262_row35_W_le_source : o262W ≤ step113_262ActualSource35 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource35
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [292, 132, 80, 12, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [292, 132, 80, 12, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [292, 132, 80, 12, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [292, 132, 80, 12, 2, 1] 1 (by decide)

private theorem step113_262s35_QtInv :
    (codeMat 419 : Mat3).transpose⁻¹ = (codeMat 183 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 419 : Mat3).transpose * (codeMat 183 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s35_source_le :
    step113_262ActualSource35 ≤ transposeW (actionW (codeMat 267) (codeMat 419) orbit35W) := by
  apply step113_262_spanCodes_le_of_gens [292, 132, 80, 12, 2, 1]
    (transposeW (actionW (codeMat 267) (codeMat 419) orbit35W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 128 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 128 (by decide)
    have hact : actionA (codeMat 267) (codeMat 419) (codeMat 128) = codeMat 448 := by
      unfold actionA; rw [step113_262s35_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 128 * (codeMat 183 : Mat3).transpose = codeMat 448
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 448 ∈ actionW (codeMat 267) (codeMat 419) orbit35W :=
      step113_262_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 448 : Mat3).transpose = codeMat 292 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h1
    have hw : codeMat 118 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 118 (by decide)
    have hact : actionA (codeMat 267) (codeMat 419) (codeMat 118) = codeMat 96 := by
      unfold actionA; rw [step113_262s35_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 118 * (codeMat 183 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 96 ∈ actionW (codeMat 267) (codeMat 419) orbit35W :=
      step113_262_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 96 : Mat3).transpose = codeMat 132 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h2
    have hw : codeMat 29 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 29 (by decide)
    have hact : actionA (codeMat 267) (codeMat 419) (codeMat 29) = codeMat 20 := by
      unfold actionA; rw [step113_262s35_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 29 * (codeMat 183 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 20 ∈ actionW (codeMat 267) (codeMat 419) orbit35W :=
      step113_262_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 20 : Mat3).transpose = codeMat 80 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h3
    have hw : codeMat 104 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 104 (by decide)
    have hact : actionA (codeMat 267) (codeMat 419) (codeMat 104) = codeMat 66 := by
      unfold actionA; rw [step113_262s35_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 104 * (codeMat 183 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 66 ∈ actionW (codeMat 267) (codeMat 419) orbit35W :=
      step113_262_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 66 : Mat3).transpose = codeMat 12 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h4
    have hw : codeMat 9 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 9 (by decide)
    have hact : actionA (codeMat 267) (codeMat 419) (codeMat 9) = codeMat 8 := by
      unfold actionA; rw [step113_262s35_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 9 * (codeMat 183 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 8 ∈ actionW (codeMat 267) (codeMat 419) orbit35W :=
      step113_262_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 8 : Mat3).transpose = codeMat 2 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h5
    have hw : codeMat 8 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 8 (by decide)
    have hact : actionA (codeMat 267) (codeMat 419) (codeMat 8) = codeMat 1 := by
      unfold actionA; rw [step113_262s35_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 8 * (codeMat 183 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 1 ∈ actionW (codeMat 267) (codeMat 419) orbit35W :=
      step113_262_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 1 : Mat3).transpose = codeMat 1 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_transposeW_of_witness hmA htrans

theorem step113_262_row35_qr : QuotientRankAtLeast step113_262ActualSource35 15 := by
  have hP : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 419 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 267) (codeMat 419) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 267) (codeMat 419) hP hQ orbit35W 15 QiushiMatmul.orbit35_lb15
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 267) (codeMat 419) orbit35W)) 15 :=
    quotientRankAtLeast_transpose hAct
  exact quotientRankAtLeast_mono step113_262s35_source_le hT

-- Source 36: row 148, orbit 55, lb 14, cap 2
def step113_262ActualSource36 : Submodule F2 Mat3 := spanCodes [336, 132, 52, 12, 2, 1]

theorem step113_262_row36_W_le_source : o262W ≤ step113_262ActualSource36 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource36
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [336, 132, 52, 12, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [336, 132, 52, 12, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [336, 132, 52, 12, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [336, 132, 52, 12, 2, 1] 1 (by decide)

private theorem step113_262s36_QtInv :
    (codeMat 309 : Mat3).transpose⁻¹ = (codeMat 309 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 309 : Mat3).transpose * (codeMat 309 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s36_source_le :
    step113_262ActualSource36 ≤ actionW (codeMat 337) (codeMat 309) o55W := by
  apply step113_262_spanCodes_le_of_gens [336, 132, 52, 12, 2, 1]
    (actionW (codeMat 337) (codeMat 309) o55W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 406 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 406 (by decide)
    have hact : actionA (codeMat 337) (codeMat 309) (codeMat 406) = codeMat 336 := by
      unfold actionA; rw [step113_262s36_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 406 * (codeMat 309 : Mat3).transpose = codeMat 336
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 133 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 133 (by decide)
    have hact : actionA (codeMat 337) (codeMat 309) (codeMat 133) = codeMat 132 := by
      unfold actionA; rw [step113_262s36_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 133 * (codeMat 309 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 47 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 47 (by decide)
    have hact : actionA (codeMat 337) (codeMat 309) (codeMat 47) = codeMat 52 := by
      unfold actionA; rw [step113_262s36_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 47 * (codeMat 309 : Mat3).transpose = codeMat 52
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 15 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 15 (by decide)
    have hact : actionA (codeMat 337) (codeMat 309) (codeMat 15) = codeMat 12 := by
      unfold actionA; rw [step113_262s36_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 15 * (codeMat 309 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 337) (codeMat 309) (codeMat 2) = codeMat 2 := by
      unfold actionA; rw [step113_262s36_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 2 * (codeMat 309 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 337) (codeMat 309) (codeMat 1) = codeMat 1 := by
      unfold actionA; rw [step113_262s36_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 1 * (codeMat 309 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row36_qr : QuotientRankAtLeast step113_262ActualSource36 14 := by
  have hP : Invertible (codeMat 337 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 309 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 337) (codeMat 309) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 337) (codeMat 309) hP hQ o55W 14 QiushiMatmul.step99_orbit55_lb14_unconditional
  exact quotientRankAtLeast_mono step113_262s36_source_le hAct

-- Source 37: row 192, orbit 7, lb 9, cap 7
def step113_262ActualSource37 : Submodule F2 Mat3 := spanCodes [256, 128, 112, 8, 4, 2, 1]

theorem step113_262_row37_W_le_source : o262W ≤ step113_262ActualSource37 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource37
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 112, 8, 4, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 112, 8, 4, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 112, 8, 4, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 112, 8, 4, 2, 1] 1 (by decide)

private theorem step113_262s37_QtInv :
    (codeMat 114 : Mat3).transpose⁻¹ = (codeMat 204 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 114 : Mat3).transpose * (codeMat 204 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s37_source_le :
    step113_262ActualSource37 ≤ actionW (codeMat 161) (codeMat 114) flatW_7 := by
  apply step113_262_spanCodes_le_of_gens [256, 128, 112, 8, 4, 2, 1]
    (actionW (codeMat 161) (codeMat 114) flatW_7)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 16 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 16 (by decide)
    have hact : actionA (codeMat 161) (codeMat 114) (codeMat 16) = codeMat 256 := by
      unfold actionA; rw [step113_262s37_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 16 * (codeMat 204 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 24 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 24 (by decide)
    have hact : actionA (codeMat 161) (codeMat 114) (codeMat 24) = codeMat 128 := by
      unfold actionA; rw [step113_262s37_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 24 * (codeMat 204 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 96 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 96 (by decide)
    have hact : actionA (codeMat 161) (codeMat 114) (codeMat 96) = codeMat 112 := by
      unfold actionA; rw [step113_262s37_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 96 * (codeMat 204 : Mat3).transpose = codeMat 112
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 161) (codeMat 114) (codeMat 256) = codeMat 8 := by
      unfold actionA; rw [step113_262s37_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 256 * (codeMat 204 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 114) (codeMat 2) = codeMat 4 := by
      unfold actionA; rw [step113_262s37_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 204 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 3 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 161) (codeMat 114) (codeMat 3) = codeMat 2 := by
      unfold actionA; rw [step113_262s37_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 3 * (codeMat 204 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 4 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 4 (by decide)
    have hact : actionA (codeMat 161) (codeMat 114) (codeMat 4) = codeMat 1 := by
      unfold actionA; rw [step113_262s37_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 4 * (codeMat 204 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row37_qr : QuotientRankAtLeast step113_262ActualSource37 9 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 114 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 114) flatW_7) 9 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 114) hP hQ flatW_7 9 QiushiMatmul.flatSeed_7
  exact quotientRankAtLeast_mono step113_262s37_source_le hAct

-- Source 38: row 331, orbit 2, lb 6, cap 10
def step113_262ActualSource38 : Submodule F2 Mat3 := spanCodes [256, 128, 96, 16, 8, 4, 2, 1]

theorem step113_262_row38_W_le_source : o262W ≤ step113_262ActualSource38 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource38
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 96, 16, 8, 4, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 96, 16, 8, 4, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 96, 16, 8, 4, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 96, 16, 8, 4, 2, 1] 1 (by decide)

private theorem step113_262s38_QtInv :
    (codeMat 98 : Mat3).transpose⁻¹ = (codeMat 140 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 98 : Mat3).transpose * (codeMat 140 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s38_source_le :
    step113_262ActualSource38 ≤ actionW (codeMat 161) (codeMat 98) flatW_2 := by
  apply step113_262_spanCodes_le_of_gens [256, 128, 96, 16, 8, 4, 2, 1]
    (actionW (codeMat 161) (codeMat 98) flatW_2)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 16 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 16 (by decide)
    have hact : actionA (codeMat 161) (codeMat 98) (codeMat 16) = codeMat 256 := by
      unfold actionA; rw [step113_262s38_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 16 * (codeMat 140 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 8 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 161) (codeMat 98) (codeMat 8) = codeMat 128 := by
      unfold actionA; rw [step113_262s38_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 8 * (codeMat 140 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 160 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 98) (codeMat 160) = codeMat 96 := by
      unfold actionA; rw [step113_262s38_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * (codeMat 140 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 64 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 64 (by decide)
    have hact : actionA (codeMat 161) (codeMat 98) (codeMat 64) = codeMat 16 := by
      unfold actionA; rw [step113_262s38_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 64 * (codeMat 140 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 256 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 161) (codeMat 98) (codeMat 256) = codeMat 8 := by
      unfold actionA; rw [step113_262s38_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 256 * (codeMat 140 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 98) (codeMat 2) = codeMat 4 := by
      unfold actionA; rw [step113_262s38_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 140 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 1 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 98) (codeMat 1) = codeMat 2 := by
      unfold actionA; rw [step113_262s38_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 140 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 4 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 4 (by decide)
    have hact : actionA (codeMat 161) (codeMat 98) (codeMat 4) = codeMat 1 := by
      unfold actionA; rw [step113_262s38_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 4 * (codeMat 140 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row38_qr : QuotientRankAtLeast step113_262ActualSource38 6 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 98) flatW_2) 6 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 98) hP hQ flatW_2 6 QiushiMatmul.flatSeed_2
  exact quotientRankAtLeast_mono step113_262s38_source_le hAct

-- Source 39: row 338, orbit 3, lb 9, cap 7
def step113_262ActualSource39 : Submodule F2 Mat3 := spanCodes [260, 132, 64, 36, 20, 12, 2, 1]

theorem step113_262_row39_W_le_source : o262W ≤ step113_262ActualSource39 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource39
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 132, 64, 36, 20, 12, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 132, 64, 36, 20, 12, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 132, 64, 36, 20, 12, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 132, 64, 36, 20, 12, 2, 1] 1 (by decide)

private theorem step113_262s39_QtInv :
    (codeMat 444 : Mat3).transpose⁻¹ = (codeMat 110 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 444 : Mat3).transpose * (codeMat 110 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s39_source_le :
    step113_262ActualSource39 ≤ actionW (codeMat 84) (codeMat 444) flatW_3 := by
  apply step113_262_spanCodes_le_of_gens [260, 132, 64, 36, 20, 12, 2, 1]
    (actionW (codeMat 84) (codeMat 444) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 455 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 455 (by decide)
    have hact : actionA (codeMat 84) (codeMat 444) (codeMat 455) = codeMat 260 := by
      unfold actionA; rw [step113_262s39_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 455 * (codeMat 110 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 454 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 454 (by decide)
    have hact : actionA (codeMat 84) (codeMat 444) (codeMat 454) = codeMat 132 := by
      unfold actionA; rw [step113_262s39_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 454 * (codeMat 110 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 444) (codeMat 2) = codeMat 64 := by
      unfold actionA; rw [step113_262s39_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 110 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 504 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 504 (by decide)
    have hact : actionA (codeMat 84) (codeMat 444) (codeMat 504) = codeMat 36 := by
      unfold actionA; rw [step113_262s39_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 504 * (codeMat 110 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 496 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 496 (by decide)
    have hact : actionA (codeMat 84) (codeMat 444) (codeMat 496) = codeMat 20 := by
      unfold actionA; rw [step113_262s39_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 496 * (codeMat 110 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 464 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 464 (by decide)
    have hact : actionA (codeMat 84) (codeMat 444) (codeMat 464) = codeMat 12 := by
      unfold actionA; rw [step113_262s39_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 464 * (codeMat 110 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 444) (codeMat 384) = codeMat 2 := by
      unfold actionA; rw [step113_262s39_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 110 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 128 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 444) (codeMat 128) = codeMat 1 := by
      unfold actionA; rw [step113_262s39_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 110 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row39_qr : QuotientRankAtLeast step113_262ActualSource39 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 444 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 444) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 444) hP hQ flatW_3 9 QiushiMatmul.flatSeed_3
  exact quotientRankAtLeast_mono step113_262s39_source_le hAct

-- Source 40: row 149, orbit 55, lb 14, cap 2
def step113_262ActualSource40 : Submodule F2 Mat3 := spanCodes [340, 132, 48, 12, 2, 1]

theorem step113_262_row40_W_le_source : o262W ≤ step113_262ActualSource40 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource40
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [340, 132, 48, 12, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [340, 132, 48, 12, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [340, 132, 48, 12, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [340, 132, 48, 12, 2, 1] 1 (by decide)

private theorem step113_262s40_QtInv :
    (codeMat 309 : Mat3).transpose⁻¹ = (codeMat 309 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 309 : Mat3).transpose * (codeMat 309 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s40_source_le :
    step113_262ActualSource40 ≤ actionW (codeMat 281) (codeMat 309) o55W := by
  apply step113_262_spanCodes_le_of_gens [340, 132, 48, 12, 2, 1]
    (actionW (codeMat 281) (codeMat 309) o55W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 405 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 405 (by decide)
    have hact : actionA (codeMat 281) (codeMat 309) (codeMat 405) = codeMat 340 := by
      unfold actionA; rw [step113_262s40_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 405 * (codeMat 309 : Mat3).transpose = codeMat 340
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 135 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 135 (by decide)
    have hact : actionA (codeMat 281) (codeMat 309) (codeMat 135) = codeMat 132 := by
      unfold actionA; rw [step113_262s40_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 135 * (codeMat 309 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 45 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 45 (by decide)
    have hact : actionA (codeMat 281) (codeMat 309) (codeMat 45) = codeMat 48 := by
      unfold actionA; rw [step113_262s40_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 45 * (codeMat 309 : Mat3).transpose = codeMat 48
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 14 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 14 (by decide)
    have hact : actionA (codeMat 281) (codeMat 309) (codeMat 14) = codeMat 12 := by
      unfold actionA; rw [step113_262s40_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 14 * (codeMat 309 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 281) (codeMat 309) (codeMat 2) = codeMat 2 := by
      unfold actionA; rw [step113_262s40_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 2 * (codeMat 309 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 281) (codeMat 309) (codeMat 1) = codeMat 1 := by
      unfold actionA; rw [step113_262s40_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 1 * (codeMat 309 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row40_qr : QuotientRankAtLeast step113_262ActualSource40 14 := by
  have hP : Invertible (codeMat 281 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 309 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 281) (codeMat 309) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 281) (codeMat 309) hP hQ o55W 14 QiushiMatmul.step99_orbit55_lb14_unconditional
  exact quotientRankAtLeast_mono step113_262s40_source_le hAct

-- Source 41: row 153, orbit 55, lb 14, cap 2
def step113_262ActualSource41 : Submodule F2 Mat3 := spanCodes [340, 132, 36, 12, 2, 1]

theorem step113_262_row41_W_le_source : o262W ≤ step113_262ActualSource41 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource41
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [340, 132, 36, 12, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [340, 132, 36, 12, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [340, 132, 36, 12, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [340, 132, 36, 12, 2, 1] 1 (by decide)

private theorem step113_262s41_QtInv :
    (codeMat 277 : Mat3).transpose⁻¹ = (codeMat 277 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 277 : Mat3).transpose * (codeMat 277 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s41_source_le :
    step113_262ActualSource41 ≤ actionW (codeMat 337) (codeMat 277) o55W := by
  apply step113_262_spanCodes_le_of_gens [340, 132, 36, 12, 2, 1]
    (actionW (codeMat 337) (codeMat 277) o55W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 273 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 273 (by decide)
    have hact : actionA (codeMat 337) (codeMat 277) (codeMat 273) = codeMat 340 := by
      unfold actionA; rw [step113_262s41_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 273 * (codeMat 277 : Mat3).transpose = codeMat 340
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 135 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 135 (by decide)
    have hact : actionA (codeMat 337) (codeMat 277) (codeMat 135) = codeMat 132 := by
      unfold actionA; rw [step113_262s41_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 135 * (codeMat 277 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 45 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 45 (by decide)
    have hact : actionA (codeMat 337) (codeMat 277) (codeMat 45) = codeMat 36 := by
      unfold actionA; rw [step113_262s41_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 45 * (codeMat 277 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 13 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 13 (by decide)
    have hact : actionA (codeMat 337) (codeMat 277) (codeMat 13) = codeMat 12 := by
      unfold actionA; rw [step113_262s41_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 13 * (codeMat 277 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 337) (codeMat 277) (codeMat 2) = codeMat 2 := by
      unfold actionA; rw [step113_262s41_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 2 * (codeMat 277 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 337) (codeMat 277) (codeMat 1) = codeMat 1 := by
      unfold actionA; rw [step113_262s41_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 1 * (codeMat 277 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row41_qr : QuotientRankAtLeast step113_262ActualSource41 14 := by
  have hP : Invertible (codeMat 337 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 277 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 337) (codeMat 277) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 337) (codeMat 277) hP hQ o55W 14 QiushiMatmul.step99_orbit55_lb14_unconditional
  exact quotientRankAtLeast_mono step113_262s41_source_le hAct

-- Source 42: row 154, orbit 55, lb 14, cap 2
def step113_262ActualSource42 : Submodule F2 Mat3 := spanCodes [256, 132, 116, 12, 2, 1]

theorem step113_262_row42_W_le_source : o262W ≤ step113_262ActualSource42 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource42
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 116, 12, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 116, 12, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 116, 12, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 116, 12, 2, 1] 1 (by decide)

private theorem step113_262s42_QtInv :
    (codeMat 270 : Mat3).transpose⁻¹ = (codeMat 298 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 270 : Mat3).transpose * (codeMat 298 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s42_source_le :
    step113_262ActualSource42 ≤ actionW (codeMat 233) (codeMat 270) o55W := by
  apply step113_262_spanCodes_le_of_gens [256, 132, 116, 12, 2, 1]
    (actionW (codeMat 233) (codeMat 270) o55W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 45 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 45 (by decide)
    have hact : actionA (codeMat 233) (codeMat 270) (codeMat 45) = codeMat 256 := by
      unfold actionA; rw [step113_262s42_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 45 * (codeMat 298 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 12 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 12 (by decide)
    have hact : actionA (codeMat 233) (codeMat 270) (codeMat 12) = codeMat 132 := by
      unfold actionA; rw [step113_262s42_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 12 * (codeMat 298 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 275 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 275 (by decide)
    have hact : actionA (codeMat 233) (codeMat 270) (codeMat 275) = codeMat 116 := by
      unfold actionA; rw [step113_262s42_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 275 * (codeMat 298 : Mat3).transpose = codeMat 116
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 135 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 135 (by decide)
    have hact : actionA (codeMat 233) (codeMat 270) (codeMat 135) = codeMat 12 := by
      unfold actionA; rw [step113_262s42_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 135 * (codeMat 298 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 233) (codeMat 270) (codeMat 1) = codeMat 2 := by
      unfold actionA; rw [step113_262s42_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 1 * (codeMat 298 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 233) (codeMat 270) (codeMat 2) = codeMat 1 := by
      unfold actionA; rw [step113_262s42_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 2 * (codeMat 298 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row42_qr : QuotientRankAtLeast step113_262ActualSource42 14 := by
  have hP : Invertible (codeMat 233 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 270 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 233) (codeMat 270) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 233) (codeMat 270) hP hQ o55W 14 QiushiMatmul.step99_orbit55_lb14_unconditional
  exact quotientRankAtLeast_mono step113_262s42_source_le hAct

-- Source 43: row 157, orbit 55, lb 14, cap 2
def step113_262ActualSource43 : Submodule F2 Mat3 := spanCodes [340, 132, 32, 12, 2, 1]

theorem step113_262_row43_W_le_source : o262W ≤ step113_262ActualSource43 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource43
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [340, 132, 32, 12, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [340, 132, 32, 12, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [340, 132, 32, 12, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [340, 132, 32, 12, 2, 1] 1 (by decide)

private theorem step113_262s43_QtInv :
    (codeMat 277 : Mat3).transpose⁻¹ = (codeMat 277 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 277 : Mat3).transpose * (codeMat 277 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s43_source_le :
    step113_262ActualSource43 ≤ actionW (codeMat 345) (codeMat 277) o55W := by
  apply step113_262_spanCodes_le_of_gens [340, 132, 32, 12, 2, 1]
    (actionW (codeMat 345) (codeMat 277) o55W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 275 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 275 (by decide)
    have hact : actionA (codeMat 345) (codeMat 277) (codeMat 275) = codeMat 340 := by
      unfold actionA; rw [step113_262s43_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 275 * (codeMat 277 : Mat3).transpose = codeMat 340
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 135 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 135 (by decide)
    have hact : actionA (codeMat 345) (codeMat 277) (codeMat 135) = codeMat 132 := by
      unfold actionA; rw [step113_262s43_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 135 * (codeMat 277 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 45 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 45 (by decide)
    have hact : actionA (codeMat 345) (codeMat 277) (codeMat 45) = codeMat 32 := by
      unfold actionA; rw [step113_262s43_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 45 * (codeMat 277 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 12 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 12 (by decide)
    have hact : actionA (codeMat 345) (codeMat 277) (codeMat 12) = codeMat 12 := by
      unfold actionA; rw [step113_262s43_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 12 * (codeMat 277 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 345) (codeMat 277) (codeMat 2) = codeMat 2 := by
      unfold actionA; rw [step113_262s43_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 2 * (codeMat 277 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 345) (codeMat 277) (codeMat 1) = codeMat 1 := by
      unfold actionA; rw [step113_262s43_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 1 * (codeMat 277 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row43_qr : QuotientRankAtLeast step113_262ActualSource43 14 := by
  have hP : Invertible (codeMat 345 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 277 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 345) (codeMat 277) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 345) (codeMat 277) hP hQ o55W 14 QiushiMatmul.step99_orbit55_lb14_unconditional
  exact quotientRankAtLeast_mono step113_262s43_source_le hAct

-- Source 44: row 185, orbit 7, lb 9, cap 7
def step113_262ActualSource44 : Submodule F2 Mat3 := spanCodes [304, 128, 112, 8, 4, 2, 1]

theorem step113_262_row44_W_le_source : o262W ≤ step113_262ActualSource44 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource44
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [304, 128, 112, 8, 4, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [304, 128, 112, 8, 4, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [304, 128, 112, 8, 4, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [304, 128, 112, 8, 4, 2, 1] 1 (by decide)

private theorem step113_262s44_QtInv :
    (codeMat 370 : Mat3).transpose⁻¹ = (codeMat 207 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 370 : Mat3).transpose * (codeMat 207 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s44_source_le :
    step113_262ActualSource44 ≤ actionW (codeMat 161) (codeMat 370) flatW_7 := by
  apply step113_262_spanCodes_le_of_gens [304, 128, 112, 8, 4, 2, 1]
    (actionW (codeMat 161) (codeMat 370) flatW_7)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 368 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 368 (by decide)
    have hact : actionA (codeMat 161) (codeMat 370) (codeMat 368) = codeMat 304 := by
      unfold actionA; rw [step113_262s44_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 368 * (codeMat 207 : Mat3).transpose = codeMat 304
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 24 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 24 (by decide)
    have hact : actionA (codeMat 161) (codeMat 370) (codeMat 24) = codeMat 128 := by
      unfold actionA; rw [step113_262s44_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 24 * (codeMat 207 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 352 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 352 (by decide)
    have hact : actionA (codeMat 161) (codeMat 370) (codeMat 352) = codeMat 112 := by
      unfold actionA; rw [step113_262s44_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 352 * (codeMat 207 : Mat3).transpose = codeMat 112
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 161) (codeMat 370) (codeMat 256) = codeMat 8 := by
      unfold actionA; rw [step113_262s44_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 256 * (codeMat 207 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 6 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 6 (by decide)
    have hact : actionA (codeMat 161) (codeMat 370) (codeMat 6) = codeMat 4 := by
      unfold actionA; rw [step113_262s44_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 6 * (codeMat 207 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 3 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 161) (codeMat 370) (codeMat 3) = codeMat 2 := by
      unfold actionA; rw [step113_262s44_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 3 * (codeMat 207 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 4 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 4 (by decide)
    have hact : actionA (codeMat 161) (codeMat 370) (codeMat 4) = codeMat 1 := by
      unfold actionA; rw [step113_262s44_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 4 * (codeMat 207 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row44_qr : QuotientRankAtLeast step113_262ActualSource44 9 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 370 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 370) flatW_7) 9 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 370) hP hQ flatW_7 9 QiushiMatmul.flatSeed_7
  exact quotientRankAtLeast_mono step113_262s44_source_le hAct

-- Source 45: row 194, orbit 7, lb 9, cap 7
def step113_262ActualSource45 : Submodule F2 Mat3 := spanCodes [336, 128, 32, 8, 4, 2, 1]

theorem step113_262_row45_W_le_source : o262W ≤ step113_262ActualSource45 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource45
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [336, 128, 32, 8, 4, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [336, 128, 32, 8, 4, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [336, 128, 32, 8, 4, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [336, 128, 32, 8, 4, 2, 1] 1 (by decide)

private theorem step113_262s45_QtInv :
    (codeMat 169 : Mat3).transpose⁻¹ = (codeMat 225 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 169 : Mat3).transpose * (codeMat 225 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s45_source_le :
    step113_262ActualSource45 ≤ actionW (codeMat 273) (codeMat 169) flatW_7 := by
  apply step113_262_spanCodes_le_of_gens [336, 128, 32, 8, 4, 2, 1]
    (actionW (codeMat 273) (codeMat 169) flatW_7)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 96 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 96 (by decide)
    have hact : actionA (codeMat 273) (codeMat 169) (codeMat 96) = codeMat 336 := by
      unfold actionA; rw [step113_262s45_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 96 * (codeMat 225 : Mat3).transpose = codeMat 336
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 256 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 273) (codeMat 169) (codeMat 256) = codeMat 128 := by
      unfold actionA; rw [step113_262s45_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 256 * (codeMat 225 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 16 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 16 (by decide)
    have hact : actionA (codeMat 273) (codeMat 169) (codeMat 16) = codeMat 32 := by
      unfold actionA; rw [step113_262s45_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 16 * (codeMat 225 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 24 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 24 (by decide)
    have hact : actionA (codeMat 273) (codeMat 169) (codeMat 24) = codeMat 8 := by
      unfold actionA; rw [step113_262s45_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 24 * (codeMat 225 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 169) (codeMat 2) = codeMat 4 := by
      unfold actionA; rw [step113_262s45_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 225 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 4 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 4 (by decide)
    have hact : actionA (codeMat 273) (codeMat 169) (codeMat 4) = codeMat 2 := by
      unfold actionA; rw [step113_262s45_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 4 * (codeMat 225 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 3 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 273) (codeMat 169) (codeMat 3) = codeMat 1 := by
      unfold actionA; rw [step113_262s45_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 3 * (codeMat 225 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row45_qr : QuotientRankAtLeast step113_262ActualSource45 9 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 169) flatW_7) 9 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 169) hP hQ flatW_7 9 QiushiMatmul.flatSeed_7
  exact quotientRankAtLeast_mono step113_262s45_source_le hAct

-- Source 46: row 309, orbit 16, lb 12, cap 4
def step113_262ActualSource46 : Submodule F2 Mat3 := spanCodes [276, 132, 84, 52, 12, 2, 1]

theorem step113_262_row46_W_le_source : o262W ≤ step113_262ActualSource46 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource46
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [276, 132, 84, 52, 12, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [276, 132, 84, 52, 12, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [276, 132, 84, 52, 12, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [276, 132, 84, 52, 12, 2, 1] 1 (by decide)

private theorem step113_262s46_QtInv :
    (codeMat 299 : Mat3).transpose⁻¹ = (codeMat 318 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 299 : Mat3).transpose * (codeMat 318 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s46_source_le :
    step113_262ActualSource46 ≤ actionW (codeMat 169) (codeMat 299) o16W_wc := by
  apply step113_262_spanCodes_le_of_gens [276, 132, 84, 52, 12, 2, 1]
    (actionW (codeMat 169) (codeMat 299) o16W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 112 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 112 (by decide)
    have hact : actionA (codeMat 169) (codeMat 299) (codeMat 112) = codeMat 276 := by
      unfold actionA; rw [step113_262s46_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 112 * (codeMat 318 : Mat3).transpose = codeMat 276
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 15 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 15 (by decide)
    have hact : actionA (codeMat 169) (codeMat 299) (codeMat 15) = codeMat 132 := by
      unfold actionA; rw [step113_262s46_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 15 * (codeMat 318 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 93 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 93 (by decide)
    have hact : actionA (codeMat 169) (codeMat 299) (codeMat 93) = codeMat 84 := by
      unfold actionA; rw [step113_262s46_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 93 * (codeMat 318 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 454 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 454 (by decide)
    have hact : actionA (codeMat 169) (codeMat 299) (codeMat 454) = codeMat 52 := by
      unfold actionA; rw [step113_262s46_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 454 * (codeMat 318 : Mat3).transpose = codeMat 52
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 198 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 198 (by decide)
    have hact : actionA (codeMat 169) (codeMat 299) (codeMat 198) = codeMat 12 := by
      unfold actionA; rw [step113_262s46_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 198 * (codeMat 318 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 299) (codeMat 1) = codeMat 2 := by
      unfold actionA; rw [step113_262s46_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * (codeMat 318 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 3 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 169) (codeMat 299) (codeMat 3) = codeMat 1 := by
      unfold actionA; rw [step113_262s46_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 3 * (codeMat 318 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row46_qr : QuotientRankAtLeast step113_262ActualSource46 12 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 299 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 299) o16W_wc) 12 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 299) hP hQ o16W_wc 12 QiushiMatmul.step109_orbit16_lb12_wc
  exact quotientRankAtLeast_mono step113_262s46_source_le hAct

-- Source 47: row 312, orbit 16, lb 12, cap 4
def step113_262ActualSource47 : Submodule F2 Mat3 := spanCodes [256, 132, 84, 32, 12, 2, 1]

theorem step113_262_row47_W_le_source : o262W ≤ step113_262ActualSource47 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource47
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 84, 32, 12, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 84, 32, 12, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 84, 32, 12, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 84, 32, 12, 2, 1] 1 (by decide)

private theorem step113_262s47_QtInv :
    (codeMat 267 : Mat3).transpose⁻¹ = (codeMat 282 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 267 : Mat3).transpose * (codeMat 282 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s47_source_le :
    step113_262ActualSource47 ≤ actionW (codeMat 161) (codeMat 267) o16W_wc := by
  apply step113_262_spanCodes_le_of_gens [256, 132, 84, 32, 12, 2, 1]
    (actionW (codeMat 161) (codeMat 267) o16W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 32 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 161) (codeMat 267) (codeMat 32) = codeMat 256 := by
      unfold actionA; rw [step113_262s47_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 32 * (codeMat 282 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 12 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 12 (by decide)
    have hact : actionA (codeMat 161) (codeMat 267) (codeMat 12) = codeMat 132 := by
      unfold actionA; rw [step113_262s47_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 12 * (codeMat 282 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 92 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 92 (by decide)
    have hact : actionA (codeMat 161) (codeMat 267) (codeMat 92) = codeMat 84 := by
      unfold actionA; rw [step113_262s47_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 92 * (codeMat 282 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 161) (codeMat 267) (codeMat 256) = codeMat 32 := by
      unfold actionA; rw [step113_262s47_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 256 * (codeMat 282 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 196 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 196 (by decide)
    have hact : actionA (codeMat 161) (codeMat 267) (codeMat 196) = codeMat 12 := by
      unfold actionA; rw [step113_262s47_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 196 * (codeMat 282 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 267) (codeMat 1) = codeMat 2 := by
      unfold actionA; rw [step113_262s47_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 282 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 3 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 161) (codeMat 267) (codeMat 3) = codeMat 1 := by
      unfold actionA; rw [step113_262s47_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 3 * (codeMat 282 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row47_qr : QuotientRankAtLeast step113_262ActualSource47 12 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 267) o16W_wc) 12 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 267) hP hQ o16W_wc 12 QiushiMatmul.step109_orbit16_lb12_wc
  exact quotientRankAtLeast_mono step113_262s47_source_le hAct

-- Source 48: row 339, orbit 3, lb 9, cap 7
def step113_262ActualSource48 : Submodule F2 Mat3 := spanCodes [256, 132, 64, 32, 20, 12, 2, 1]

theorem step113_262_row48_W_le_source : o262W ≤ step113_262ActualSource48 := by
  unfold o262W
  apply step113_262_spanCodes_le_of_gens [132, 12, 2, 1] step113_262ActualSource48
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 32, 20, 12, 2, 1] 132 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 32, 20, 12, 2, 1] 12 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 32, 20, 12, 2, 1] 2 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 32, 20, 12, 2, 1] 1 (by decide)

private theorem step113_262s48_QtInv :
    (codeMat 156 : Mat3).transpose⁻¹ = (codeMat 102 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 156 : Mat3).transpose * (codeMat 102 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_262s48_source_le :
    step113_262ActualSource48 ≤ actionW (codeMat 84) (codeMat 156) flatW_3 := by
  apply step113_262_spanCodes_le_of_gens [256, 132, 64, 32, 20, 12, 2, 1]
    (actionW (codeMat 84) (codeMat 156) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 1 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 156) (codeMat 1) = codeMat 256 := by
      unfold actionA; rw [step113_262s48_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 102 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 70 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 70 (by decide)
    have hact : actionA (codeMat 84) (codeMat 156) (codeMat 70) = codeMat 132 := by
      unfold actionA; rw [step113_262s48_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 70 * (codeMat 102 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 156) (codeMat 2) = codeMat 64 := by
      unfold actionA; rw [step113_262s48_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 102 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 156) (codeMat 8) = codeMat 32 := by
      unfold actionA; rw [step113_262s48_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 102 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 112 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 112 (by decide)
    have hact : actionA (codeMat 84) (codeMat 156) (codeMat 112) = codeMat 20 := by
      unfold actionA; rw [step113_262s48_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 112 * (codeMat 102 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 80 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 80 (by decide)
    have hact : actionA (codeMat 84) (codeMat 156) (codeMat 80) = codeMat 12 := by
      unfold actionA; rw [step113_262s48_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 80 * (codeMat 102 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 156) (codeMat 384) = codeMat 2 := by
      unfold actionA; rw [step113_262s48_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 102 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 128 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 156) (codeMat 128) = codeMat 1 := by
      unfold actionA; rw [step113_262s48_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 102 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_262_codeMat_mem_actionW_of_witness hw hact

theorem step113_262_row48_qr : QuotientRankAtLeast step113_262ActualSource48 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 156 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 156) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 156) hP hQ flatW_3 9 QiushiMatmul.flatSeed_3
  exact quotientRankAtLeast_mono step113_262s48_source_le hAct

/-- Preceding lower bound for zero-fiber elimination, using compressed row 23. -/
theorem step113_262_base_lb16 : QuotientRankAtLeast o262W 16 :=
  quotientRankAtLeast_mono step113_262_row23_W_le_source step113_262_row23_qr

/-- All 49 source row lower bounds. -/
theorem step113_262_row_qr (i : Fin 49) : QuotientRankAtLeast
    (match i.val with
    | 0 => step113_262ActualSource0
    | 1 => step113_262ActualSource1
    | 2 => step113_262ActualSource2
    | 3 => step113_262ActualSource3
    | 4 => step113_262ActualSource4
    | 5 => step113_262ActualSource5
    | 6 => step113_262ActualSource6
    | 7 => step113_262ActualSource7
    | 8 => step113_262ActualSource8
    | 9 => step113_262ActualSource9
    | 10 => step113_262ActualSource10
    | 11 => step113_262ActualSource11
    | 12 => step113_262ActualSource12
    | 13 => step113_262ActualSource13
    | 14 => step113_262ActualSource14
    | 15 => step113_262ActualSource15
    | 16 => step113_262ActualSource16
    | 17 => step113_262ActualSource17
    | 18 => step113_262ActualSource18
    | 19 => step113_262ActualSource19
    | 20 => step113_262ActualSource20
    | 21 => step113_262ActualSource21
    | 22 => step113_262ActualSource22
    | 23 => step113_262ActualSource23
    | 24 => step113_262ActualSource24
    | 25 => step113_262ActualSource25
    | 26 => step113_262ActualSource26
    | 27 => step113_262ActualSource27
    | 28 => step113_262ActualSource28
    | 29 => step113_262ActualSource29
    | 30 => step113_262ActualSource30
    | 31 => step113_262ActualSource31
    | 32 => step113_262ActualSource32
    | 33 => step113_262ActualSource33
    | 34 => step113_262ActualSource34
    | 35 => step113_262ActualSource35
    | 36 => step113_262ActualSource36
    | 37 => step113_262ActualSource37
    | 38 => step113_262ActualSource38
    | 39 => step113_262ActualSource39
    | 40 => step113_262ActualSource40
    | 41 => step113_262ActualSource41
    | 42 => step113_262ActualSource42
    | 43 => step113_262ActualSource43
    | 44 => step113_262ActualSource44
    | 45 => step113_262ActualSource45
    | 46 => step113_262ActualSource46
    | 47 => step113_262ActualSource47
    | 48 => step113_262ActualSource48
    | _ => step113_262ActualSource0)
    (match i.val with
    | 0 => 12
    | 1 => 15
    | 2 => 15
    | 3 => 15
    | 4 => 15
    | 5 => 15
    | 6 => 15
    | 7 => 15
    | 8 => 15
    | 9 => 15
    | 10 => 15
    | 11 => 14
    | 12 => 14
    | 13 => 9
    | 14 => 9
    | 15 => 12
    | 16 => 12
    | 17 => 6
    | 18 => 6
    | 19 => 6
    | 20 => 6
    | 21 => 9
    | 22 => 9
    | 23 => 16
    | 24 => 15
    | 25 => 15
    | 26 => 15
    | 27 => 9
    | 28 => 9
    | 29 => 12
    | 30 => 12
    | 31 => 6
    | 32 => 6
    | 33 => 9
    | 34 => 9
    | 35 => 15
    | 36 => 14
    | 37 => 9
    | 38 => 6
    | 39 => 9
    | 40 => 14
    | 41 => 14
    | 42 => 14
    | 43 => 14
    | 44 => 9
    | 45 => 9
    | 46 => 12
    | 47 => 12
    | 48 => 9
    | _ => 12) := by
  fin_cases i
  · exact step113_262_row0_qr
  · exact step113_262_row1_qr
  · exact step113_262_row2_qr
  · exact step113_262_row3_qr
  · exact step113_262_row4_qr
  · exact step113_262_row5_qr
  · exact step113_262_row6_qr
  · exact step113_262_row7_qr
  · exact step113_262_row8_qr
  · exact step113_262_row9_qr
  · exact step113_262_row10_qr
  · exact step113_262_row11_qr
  · exact step113_262_row12_qr
  · exact step113_262_row13_qr
  · exact step113_262_row14_qr
  · exact step113_262_row15_qr
  · exact step113_262_row16_qr
  · exact step113_262_row17_qr
  · exact step113_262_row18_qr
  · exact step113_262_row19_qr
  · exact step113_262_row20_qr
  · exact step113_262_row21_qr
  · exact step113_262_row22_qr
  · exact step113_262_row23_qr
  · exact step113_262_row24_qr
  · exact step113_262_row25_qr
  · exact step113_262_row26_qr
  · exact step113_262_row27_qr
  · exact step113_262_row28_qr
  · exact step113_262_row29_qr
  · exact step113_262_row30_qr
  · exact step113_262_row31_qr
  · exact step113_262_row32_qr
  · exact step113_262_row33_qr
  · exact step113_262_row34_qr
  · exact step113_262_row35_qr
  · exact step113_262_row36_qr
  · exact step113_262_row37_qr
  · exact step113_262_row38_qr
  · exact step113_262_row39_qr
  · exact step113_262_row40_qr
  · exact step113_262_row41_qr
  · exact step113_262_row42_qr
  · exact step113_262_row43_qr
  · exact step113_262_row44_qr
  · exact step113_262_row45_qr
  · exact step113_262_row46_qr
  · exact step113_262_row47_qr
  · exact step113_262_row48_qr

end QiushiMatmul
