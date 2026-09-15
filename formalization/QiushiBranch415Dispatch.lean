import Mathlib
import QiushiCodeSpanCore
import QiushiFlattenSeeds
import QiushiMonoOrbit103From35T
import QiushiMonoOrbit134From35T
import QiushiMonotonicity
import QiushiOrbit101FP
import QiushiOrbit10FP
import QiushiOrbit14FP
import QiushiOrbit29FP
import QiushiOrbit35FP
import QiushiOrbit5FP
import QiushiOrbitTransport
import QiushiStep99Orbit144Dispatch
import QiushiTransposeTransport
import QiushiWcOrbit141Dispatch
import QiushiWcOrbit146Dispatch
import QiushiWcOrbit25Dispatch

set_option maxHeartbeats 800000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step113_415_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by intro M hM; rcases hM with ⟨n, hn, rfl⟩; exact h n hn)

private theorem step113_415_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  exact ⟨codeMat witness, h_mem, h_action⟩

private theorem step113_415_codeMat_mem_transposeW_of_witness
    {V : Submodule F2 Mat3} {pre tpre : Nat}
    (h_mem : codeMat tpre ∈ V)
    (h_trans : (codeMat tpre : Mat3).transpose = codeMat pre) :
    codeMat pre ∈ transposeW V := by
  exact ⟨codeMat tpre, h_mem, h_trans⟩

/-- Orbit 415 quotient kernel. -/
def o415W : Submodule F2 Mat3 := spanCodes [273, 4, 2]

-- Source 0: row 29, orbit 101, lb 15, cap 1
def step113_415ActualSource0 : Submodule F2 Mat3 := spanCodes [273, 32, 9, 4, 2]

theorem step113_415_row0_W_le_source : o415W ≤ step113_415ActualSource0 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource0
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 32, 9, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 32, 9, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 32, 9, 4, 2] 2 (by decide)

private theorem step113_415s0_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s0_source_le :
    step113_415ActualSource0 ≤ actionW (codeMat 267) (codeMat 140) orbit101W := by
  apply step113_415_spanCodes_le_of_gens [273, 32, 9, 4, 2]
    (actionW (codeMat 267) (codeMat 140) orbit101W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 116 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 116 (by decide)
    have hact : actionA (codeMat 267) (codeMat 140) (codeMat 116) = codeMat 273 := by
      unfold actionA; rw [step113_415s0_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 116 * (codeMat 98 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 9 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 9 (by decide)
    have hact : actionA (codeMat 267) (codeMat 140) (codeMat 9) = codeMat 32 := by
      unfold actionA; rw [step113_415s0_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 9 * (codeMat 98 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 2 (by decide)
    have hact : actionA (codeMat 267) (codeMat 140) (codeMat 2) = codeMat 9 := by
      unfold actionA; rw [step113_415s0_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 2 * (codeMat 98 : Mat3).transpose = codeMat 9
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 8 (by decide)
    have hact : actionA (codeMat 267) (codeMat 140) (codeMat 8) = codeMat 4 := by
      unfold actionA; rw [step113_415s0_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 32 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 32 (by decide)
    have hact : actionA (codeMat 267) (codeMat 140) (codeMat 32) = codeMat 2 := by
      unfold actionA; rw [step113_415s0_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 32 * (codeMat 98 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row0_qr : QuotientRankAtLeast step113_415ActualSource0 15 := by
  have hP : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 267) (codeMat 140) orbit101W) 15 :=
    @quotientRankAtLeast_action (codeMat 267) (codeMat 140) hP hQ orbit101W 15 QiushiMatmul.orbit101_lb15
  exact quotientRankAtLeast_mono step113_415s0_source_le hAct

-- Source 1: row 30, orbit 101, lb 15, cap 1
def step113_415ActualSource1 : Submodule F2 Mat3 := spanCodes [265, 32, 24, 4, 2]

theorem step113_415_row1_W_le_source : o415W ≤ step113_415ActualSource1 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource1
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [265, 32, 24, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [265, 32, 24, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [265, 32, 24, 4, 2] 2 (by decide)

private theorem step113_415s1_QtInv :
    (codeMat 204 : Mat3).transpose⁻¹ = (codeMat 114 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 204 : Mat3).transpose * (codeMat 114 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s1_source_le :
    step113_415ActualSource1 ≤ actionW (codeMat 266) (codeMat 204) orbit101W := by
  apply step113_415_spanCodes_le_of_gens [265, 32, 24, 4, 2]
    (actionW (codeMat 266) (codeMat 204) orbit101W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 118 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 118 (by decide)
    have hact : actionA (codeMat 266) (codeMat 204) (codeMat 118) = codeMat 265 := by
      unfold actionA; rw [step113_415s1_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 118 * (codeMat 114 : Mat3).transpose = codeMat 265
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 204) (codeMat 1) = codeMat 32 := by
      unfold actionA; rw [step113_415s1_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 114 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 204) (codeMat 2) = codeMat 24 := by
      unfold actionA; rw [step113_415s1_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 114 : Mat3).transpose = codeMat 24
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 204) (codeMat 8) = codeMat 4 := by
      unfold actionA; rw [step113_415s1_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 114 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 32 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 32 (by decide)
    have hact : actionA (codeMat 266) (codeMat 204) (codeMat 32) = codeMat 2 := by
      unfold actionA; rw [step113_415s1_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 114 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row1_qr : QuotientRankAtLeast step113_415ActualSource1 15 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 204 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 204) orbit101W) 15 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 204) hP hQ orbit101W 15 QiushiMatmul.orbit101_lb15
  exact quotientRankAtLeast_mono step113_415s1_source_le hAct

-- Source 2: row 31, orbit 101, lb 15, cap 1
def step113_415ActualSource2 : Submodule F2 Mat3 := spanCodes [264, 32, 25, 4, 2]

theorem step113_415_row2_W_le_source : o415W ≤ step113_415ActualSource2 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource2
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [264, 32, 25, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [264, 32, 25, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [264, 32, 25, 4, 2] 2 (by decide)

private theorem step113_415s2_QtInv :
    (codeMat 204 : Mat3).transpose⁻¹ = (codeMat 114 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 204 : Mat3).transpose * (codeMat 114 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s2_source_le :
    step113_415ActualSource2 ≤ actionW (codeMat 267) (codeMat 204) orbit101W := by
  apply step113_415_spanCodes_le_of_gens [264, 32, 25, 4, 2]
    (actionW (codeMat 267) (codeMat 204) orbit101W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 118 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 118 (by decide)
    have hact : actionA (codeMat 267) (codeMat 204) (codeMat 118) = codeMat 264 := by
      unfold actionA; rw [step113_415s2_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 118 * (codeMat 114 : Mat3).transpose = codeMat 264
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 9 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 9 (by decide)
    have hact : actionA (codeMat 267) (codeMat 204) (codeMat 9) = codeMat 32 := by
      unfold actionA; rw [step113_415s2_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 9 * (codeMat 114 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 34 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 34 (by decide)
    have hact : actionA (codeMat 267) (codeMat 204) (codeMat 34) = codeMat 25 := by
      unfold actionA; rw [step113_415s2_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 34 * (codeMat 114 : Mat3).transpose = codeMat 25
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 8 (by decide)
    have hact : actionA (codeMat 267) (codeMat 204) (codeMat 8) = codeMat 4 := by
      unfold actionA; rw [step113_415s2_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 8 * (codeMat 114 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 32 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 32 (by decide)
    have hact : actionA (codeMat 267) (codeMat 204) (codeMat 32) = codeMat 2 := by
      unfold actionA; rw [step113_415s2_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 32 * (codeMat 114 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row2_qr : QuotientRankAtLeast step113_415ActualSource2 15 := by
  have hP : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 204 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 267) (codeMat 204) orbit101W) 15 :=
    @quotientRankAtLeast_action (codeMat 267) (codeMat 204) hP hQ orbit101W 15 QiushiMatmul.orbit101_lb15
  exact quotientRankAtLeast_mono step113_415s2_source_le hAct

-- Source 3: row 42, orbit 101, lb 15, cap 1
def step113_415ActualSource3 : Submodule F2 Mat3 := spanCodes [273, 128, 65, 4, 2]

theorem step113_415_row3_W_le_source : o415W ≤ step113_415ActualSource3 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource3
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 128, 65, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 128, 65, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 128, 65, 4, 2] 2 (by decide)

private theorem step113_415s3_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s3_source_le :
    step113_415ActualSource3 ≤ actionW (codeMat 141) (codeMat 266) orbit101W := by
  apply step113_415_spanCodes_le_of_gens [273, 128, 65, 4, 2]
    (actionW (codeMat 141) (codeMat 266) orbit101W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 116 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 116 (by decide)
    have hact : actionA (codeMat 141) (codeMat 266) (codeMat 116) = codeMat 273 := by
      unfold actionA; rw [step113_415s3_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 116 * (codeMat 266 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 9 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 9 (by decide)
    have hact : actionA (codeMat 141) (codeMat 266) (codeMat 9) = codeMat 128 := by
      unfold actionA; rw [step113_415s3_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 9 * (codeMat 266 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 2 (by decide)
    have hact : actionA (codeMat 141) (codeMat 266) (codeMat 2) = codeMat 65 := by
      unfold actionA; rw [step113_415s3_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 2 * (codeMat 266 : Mat3).transpose = codeMat 65
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 32 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 32 (by decide)
    have hact : actionA (codeMat 141) (codeMat 266) (codeMat 32) = codeMat 4 := by
      unfold actionA; rw [step113_415s3_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 32 * (codeMat 266 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 8 (by decide)
    have hact : actionA (codeMat 141) (codeMat 266) (codeMat 8) = codeMat 2 := by
      unfold actionA; rw [step113_415s3_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 8 * (codeMat 266 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row3_qr : QuotientRankAtLeast step113_415ActualSource3 15 := by
  have hP : Invertible (codeMat 141 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 141) (codeMat 266) orbit101W) 15 :=
    @quotientRankAtLeast_action (codeMat 141) (codeMat 266) hP hQ orbit101W 15 QiushiMatmul.orbit101_lb15
  exact quotientRankAtLeast_mono step113_415s3_source_le hAct

-- Source 4: row 47, orbit 101, lb 15, cap 1
def step113_415ActualSource4 : Submodule F2 Mat3 := spanCodes [273, 161, 73, 4, 2]

theorem step113_415_row4_W_le_source : o415W ≤ step113_415ActualSource4 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource4
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 161, 73, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 161, 73, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 161, 73, 4, 2] 2 (by decide)

private theorem step113_415s4_QtInv :
    (codeMat 394 : Mat3).transpose⁻¹ = (codeMat 330 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 394 : Mat3).transpose * (codeMat 330 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s4_source_le :
    step113_415ActualSource4 ≤ actionW (codeMat 143) (codeMat 394) orbit101W := by
  apply step113_415_spanCodes_le_of_gens [273, 161, 73, 4, 2]
    (actionW (codeMat 143) (codeMat 394) orbit101W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 116 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 116 (by decide)
    have hact : actionA (codeMat 143) (codeMat 394) (codeMat 116) = codeMat 273 := by
      unfold actionA; rw [step113_415s4_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 116 * (codeMat 330 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 125 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 125 (by decide)
    have hact : actionA (codeMat 143) (codeMat 394) (codeMat 125) = codeMat 161 := by
      unfold actionA; rw [step113_415s4_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 125 * (codeMat 330 : Mat3).transpose = codeMat 161
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 2 (by decide)
    have hact : actionA (codeMat 143) (codeMat 394) (codeMat 2) = codeMat 73 := by
      unfold actionA; rw [step113_415s4_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 2 * (codeMat 330 : Mat3).transpose = codeMat 73
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 32 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 32 (by decide)
    have hact : actionA (codeMat 143) (codeMat 394) (codeMat 32) = codeMat 4 := by
      unfold actionA; rw [step113_415s4_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 32 * (codeMat 330 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 40 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 40 (by decide)
    have hact : actionA (codeMat 143) (codeMat 394) (codeMat 40) = codeMat 2 := by
      unfold actionA; rw [step113_415s4_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 40 * (codeMat 330 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row4_qr : QuotientRankAtLeast step113_415ActualSource4 15 := by
  have hP : Invertible (codeMat 143 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 394 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 143) (codeMat 394) orbit101W) 15 :=
    @quotientRankAtLeast_action (codeMat 143) (codeMat 394) hP hQ orbit101W 15 QiushiMatmul.orbit101_lb15
  exact quotientRankAtLeast_mono step113_415s4_source_le hAct

-- Source 5: row 327, orbit 141, lb 15, cap 1
def step113_415ActualSource5 : Submodule F2 Mat3 := spanCodes [273, 169, 80, 4, 2]

theorem step113_415_row5_W_le_source : o415W ≤ step113_415ActualSource5 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource5
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 169, 80, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 169, 80, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 169, 80, 4, 2] 2 (by decide)

private theorem step113_415s5_QtInv :
    (codeMat 106 : Mat3).transpose⁻¹ = (codeMat 396 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 106 : Mat3).transpose * (codeMat 396 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s5_source_le :
    step113_415ActualSource5 ≤ actionW (codeMat 233) (codeMat 106) o141W_wc := by
  apply step113_415_spanCodes_le_of_gens [273, 169, 80, 4, 2]
    (actionW (codeMat 233) (codeMat 106) o141W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 85 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 85 (by decide)
    have hact : actionA (codeMat 233) (codeMat 106) (codeMat 85) = codeMat 273 := by
      unfold actionA; rw [step113_415s5_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 85 * (codeMat 396 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 267 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 267 (by decide)
    have hact : actionA (codeMat 233) (codeMat 106) (codeMat 267) = codeMat 169 := by
      unfold actionA; rw [step113_415s5_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 267 * (codeMat 396 : Mat3).transpose = codeMat 169
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 119 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 119 (by decide)
    have hact : actionA (codeMat 233) (codeMat 106) (codeMat 119) = codeMat 80 := by
      unfold actionA; rw [step113_415s5_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 119 * (codeMat 396 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 233) (codeMat 106) (codeMat 2) = codeMat 4 := by
      unfold actionA; rw [step113_415s5_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 2 * (codeMat 396 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 233) (codeMat 106) (codeMat 1) = codeMat 2 := by
      unfold actionA; rw [step113_415s5_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 1 * (codeMat 396 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row5_qr : QuotientRankAtLeast step113_415ActualSource5 15 := by
  have hP : Invertible (codeMat 233 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 106 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 233) (codeMat 106) o141W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 233) (codeMat 106) hP hQ o141W_wc 15 QiushiMatmul.step109_orbit141_lb15_wc
  exact quotientRankAtLeast_mono step113_415s5_source_le hAct

-- Source 6: row 465, orbit 144, lb 15, cap 1
def step113_415ActualSource6 : Submodule F2 Mat3 := spanCodes [273, 169, 112, 4, 2]

theorem step113_415_row6_W_le_source : o415W ≤ step113_415ActualSource6 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource6
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 169, 112, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 169, 112, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 169, 112, 4, 2] 2 (by decide)

private theorem step113_415s6_QtInv :
    (codeMat 123 : Mat3).transpose⁻¹ = (codeMat 236 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 123 : Mat3).transpose * (codeMat 236 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s6_source_le :
    step113_415ActualSource6 ≤ actionW (codeMat 249) (codeMat 123) o144W := by
  apply step113_415_spanCodes_le_of_gens [273, 169, 112, 4, 2]
    (actionW (codeMat 249) (codeMat 123) o144W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 84 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 84 (by decide)
    have hact : actionA (codeMat 249) (codeMat 123) (codeMat 84) = codeMat 273 := by
      unfold actionA; rw [step113_415s6_QtInv]
      show (codeMat 249 : Mat3).transpose * codeMat 84 * (codeMat 236 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 410 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 410 (by decide)
    have hact : actionA (codeMat 249) (codeMat 123) (codeMat 410) = codeMat 169 := by
      unfold actionA; rw [step113_415s6_QtInv]
      show (codeMat 249 : Mat3).transpose * codeMat 410 * (codeMat 236 : Mat3).transpose = codeMat 169
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 441 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 441 (by decide)
    have hact : actionA (codeMat 249) (codeMat 123) (codeMat 441) = codeMat 112 := by
      unfold actionA; rw [step113_415s6_QtInv]
      show (codeMat 249 : Mat3).transpose * codeMat 441 * (codeMat 236 : Mat3).transpose = codeMat 112
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 249) (codeMat 123) (codeMat 2) = codeMat 4 := by
      unfold actionA; rw [step113_415s6_QtInv]
      show (codeMat 249 : Mat3).transpose * codeMat 2 * (codeMat 236 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 249) (codeMat 123) (codeMat 3) = codeMat 2 := by
      unfold actionA; rw [step113_415s6_QtInv]
      show (codeMat 249 : Mat3).transpose * codeMat 3 * (codeMat 236 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row6_qr : QuotientRankAtLeast step113_415ActualSource6 15 := by
  have hP : Invertible (codeMat 249 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 123 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 249) (codeMat 123) o144W) 15 :=
    @quotientRankAtLeast_action (codeMat 249) (codeMat 123) hP hQ o144W 15 QiushiMatmul.step99_orbit144_lb15_unconditional
  exact quotientRankAtLeast_mono step113_415s6_source_le hAct

-- Source 7: row 512, orbit 146, lb 15, cap 1
def step113_415ActualSource7 : Submodule F2 Mat3 := spanCodes [273, 168, 89, 4, 2]

theorem step113_415_row7_W_le_source : o415W ≤ step113_415ActualSource7 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource7
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 168, 89, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 168, 89, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 168, 89, 4, 2] 2 (by decide)

private theorem step113_415s7_QtInv :
    (codeMat 107 : Mat3).transpose⁻¹ = (codeMat 428 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 107 : Mat3).transpose * (codeMat 428 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s7_source_le :
    step113_415ActualSource7 ≤ actionW (codeMat 225) (codeMat 107) o146W_wc := by
  apply step113_415_spanCodes_le_of_gens [273, 168, 89, 4, 2]
    (actionW (codeMat 225) (codeMat 107) o146W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 86 ∈ o146W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [280, 160, 84, 2, 1] 86 (by decide)
    have hact : actionA (codeMat 225) (codeMat 107) (codeMat 86) = codeMat 273 := by
      unfold actionA; rw [step113_415s7_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 86 * (codeMat 428 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 333 ∈ o146W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [280, 160, 84, 2, 1] 333 (by decide)
    have hact : actionA (codeMat 225) (codeMat 107) (codeMat 333) = codeMat 168 := by
      unfold actionA; rw [step113_415s7_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 333 * (codeMat 428 : Mat3).transpose = codeMat 168
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 441 ∈ o146W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [280, 160, 84, 2, 1] 441 (by decide)
    have hact : actionA (codeMat 225) (codeMat 107) (codeMat 441) = codeMat 89 := by
      unfold actionA; rw [step113_415s7_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 441 * (codeMat 428 : Mat3).transpose = codeMat 89
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ o146W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [280, 160, 84, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 225) (codeMat 107) (codeMat 2) = codeMat 4 := by
      unfold actionA; rw [step113_415s7_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 2 * (codeMat 428 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o146W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [280, 160, 84, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 225) (codeMat 107) (codeMat 1) = codeMat 2 := by
      unfold actionA; rw [step113_415s7_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 1 * (codeMat 428 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row7_qr : QuotientRankAtLeast step113_415ActualSource7 15 := by
  have hP : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 107 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 225) (codeMat 107) o146W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 225) (codeMat 107) hP hQ o146W_wc 15 QiushiMatmul.step109_orbit146_lb15_wc
  exact quotientRankAtLeast_mono step113_415s7_source_le hAct

-- Source 8: row 594, orbit 25, lb 11, cap 5
def step113_415ActualSource8 : Submodule F2 Mat3 := spanCodes [272, 80, 8, 4, 2, 1]

theorem step113_415_row8_W_le_source : o415W ≤ step113_415ActualSource8 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource8
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 80, 8, 4, 2, 1] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 80, 8, 4, 2, 1] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 80, 8, 4, 2, 1] 2 (by decide)

private theorem step113_415s8_QtInv :
    (codeMat 277 : Mat3).transpose⁻¹ = (codeMat 277 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 277 : Mat3).transpose * (codeMat 277 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s8_source_le :
    step113_415ActualSource8 ≤ actionW (codeMat 273) (codeMat 277) o25W_wc := by
  apply step113_415_spanCodes_le_of_gens [272, 80, 8, 4, 2, 1]
    (actionW (codeMat 273) (codeMat 277) o25W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 336 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 336 (by decide)
    have hact : actionA (codeMat 273) (codeMat 277) (codeMat 336) = codeMat 272 := by
      unfold actionA; rw [step113_415s8_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 336 * (codeMat 277 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 80 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 80 (by decide)
    have hact : actionA (codeMat 273) (codeMat 277) (codeMat 80) = codeMat 80 := by
      unfold actionA; rw [step113_415s8_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 80 * (codeMat 277 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 277) (codeMat 8) = codeMat 8 := by
      unfold actionA; rw [step113_415s8_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 277 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 5 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 5 (by decide)
    have hact : actionA (codeMat 273) (codeMat 277) (codeMat 5) = codeMat 4 := by
      unfold actionA; rw [step113_415s8_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 5 * (codeMat 277 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 277) (codeMat 2) = codeMat 2 := by
      unfold actionA; rw [step113_415s8_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 277 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 277) (codeMat 1) = codeMat 1 := by
      unfold actionA; rw [step113_415s8_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 277 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row8_qr : QuotientRankAtLeast step113_415ActualSource8 11 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 277 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 277) o25W_wc) 11 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 277) hP hQ o25W_wc 11 QiushiMatmul.step109_orbit25_lb11_wc
  exact quotientRankAtLeast_mono step113_415s8_source_le hAct

-- Source 9: row 603, orbit 25, lb 11, cap 5
def step113_415ActualSource9 : Submodule F2 Mat3 := spanCodes [272, 72, 56, 4, 2, 1]

theorem step113_415_row9_W_le_source : o415W ≤ step113_415ActualSource9 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource9
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 72, 56, 4, 2, 1] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 72, 56, 4, 2, 1] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 72, 56, 4, 2, 1] 2 (by decide)

private theorem step113_415s9_QtInv :
    (codeMat 179 : Mat3).transpose⁻¹ = (codeMat 421 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 179 : Mat3).transpose * (codeMat 421 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s9_source_le :
    step113_415ActualSource9 ≤ actionW (codeMat 177) (codeMat 179) o25W_wc := by
  apply step113_415_spanCodes_le_of_gens [272, 72, 56, 4, 2, 1]
    (actionW (codeMat 177) (codeMat 179) o25W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 336 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 336 (by decide)
    have hact : actionA (codeMat 177) (codeMat 179) (codeMat 336) = codeMat 272 := by
      unfold actionA; rw [step113_415s9_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 336 * (codeMat 421 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 8 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 177) (codeMat 179) (codeMat 8) = codeMat 72 := by
      unfold actionA; rw [step113_415s9_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 8 * (codeMat 421 : Mat3).transpose = codeMat 72
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 256 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 177) (codeMat 179) (codeMat 256) = codeMat 56 := by
      unfold actionA; rw [step113_415s9_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 256 * (codeMat 421 : Mat3).transpose = codeMat 56
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 177) (codeMat 179) (codeMat 2) = codeMat 4 := by
      unfold actionA; rw [step113_415s9_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 2 * (codeMat 421 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 7 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 7 (by decide)
    have hact : actionA (codeMat 177) (codeMat 179) (codeMat 7) = codeMat 2 := by
      unfold actionA; rw [step113_415s9_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 7 * (codeMat 421 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 179) (codeMat 1) = codeMat 1 := by
      unfold actionA; rw [step113_415s9_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * (codeMat 421 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row9_qr : QuotientRankAtLeast step113_415ActualSource9 11 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 179 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 179) o25W_wc) 11 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 179) hP hQ o25W_wc 11 QiushiMatmul.step109_orbit25_lb11_wc
  exact quotientRankAtLeast_mono step113_415s9_source_le hAct

-- Source 10: row 644, orbit 25, lb 11, cap 5
def step113_415ActualSource10 : Submodule F2 Mat3 := spanCodes [272, 136, 80, 4, 2, 1]

theorem step113_415_row10_W_le_source : o415W ≤ step113_415ActualSource10 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource10
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 136, 80, 4, 2, 1] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 136, 80, 4, 2, 1] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 136, 80, 4, 2, 1] 2 (by decide)

private theorem step113_415s10_QtInv :
    (codeMat 314 : Mat3).transpose⁻¹ = (codeMat 271 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 314 : Mat3).transpose * (codeMat 271 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s10_source_le :
    step113_415ActualSource10 ≤ actionW (codeMat 305) (codeMat 314) o25W_wc := by
  apply step113_415_spanCodes_le_of_gens [272, 136, 80, 4, 2, 1]
    (actionW (codeMat 305) (codeMat 314) o25W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 344 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 344 (by decide)
    have hact : actionA (codeMat 305) (codeMat 314) (codeMat 344) = codeMat 272 := by
      unfold actionA; rw [step113_415s10_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 344 * (codeMat 271 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 80 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 80 (by decide)
    have hact : actionA (codeMat 305) (codeMat 314) (codeMat 80) = codeMat 136 := by
      unfold actionA; rw [step113_415s10_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 80 * (codeMat 271 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 88 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 88 (by decide)
    have hact : actionA (codeMat 305) (codeMat 314) (codeMat 88) = codeMat 80 := by
      unfold actionA; rw [step113_415s10_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 88 * (codeMat 271 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 6 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 6 (by decide)
    have hact : actionA (codeMat 305) (codeMat 314) (codeMat 6) = codeMat 4 := by
      unfold actionA; rw [step113_415s10_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 6 * (codeMat 271 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 305) (codeMat 314) (codeMat 3) = codeMat 2 := by
      unfold actionA; rw [step113_415s10_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 3 * (codeMat 271 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 305) (codeMat 314) (codeMat 2) = codeMat 1 := by
      unfold actionA; rw [step113_415s10_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 2 * (codeMat 271 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row10_qr : QuotientRankAtLeast step113_415ActualSource10 11 := by
  have hP : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 314 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 305) (codeMat 314) o25W_wc) 11 :=
    @quotientRankAtLeast_action (codeMat 305) (codeMat 314) hP hQ o25W_wc 11 QiushiMatmul.step109_orbit25_lb11_wc
  exact quotientRankAtLeast_mono step113_415s10_source_le hAct

-- Source 11: row 645, orbit 25, lb 11, cap 5
def step113_415ActualSource11 : Submodule F2 Mat3 := spanCodes [272, 152, 64, 4, 2, 1]

theorem step113_415_row11_W_le_source : o415W ≤ step113_415ActualSource11 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource11
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 152, 64, 4, 2, 1] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 152, 64, 4, 2, 1] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 152, 64, 4, 2, 1] 2 (by decide)

private theorem step113_415s11_QtInv :
    (codeMat 419 : Mat3).transpose⁻¹ = (codeMat 183 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 419 : Mat3).transpose * (codeMat 183 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s11_source_le :
    step113_415ActualSource11 ≤ actionW (codeMat 417) (codeMat 419) o25W_wc := by
  apply step113_415_spanCodes_le_of_gens [272, 152, 64, 4, 2, 1]
    (actionW (codeMat 417) (codeMat 419) o25W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 344 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 344 (by decide)
    have hact : actionA (codeMat 417) (codeMat 419) (codeMat 344) = codeMat 272 := by
      unfold actionA; rw [step113_415s11_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 344 * (codeMat 183 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 264 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 264 (by decide)
    have hact : actionA (codeMat 417) (codeMat 419) (codeMat 264) = codeMat 152 := by
      unfold actionA; rw [step113_415s11_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 264 * (codeMat 183 : Mat3).transpose = codeMat 152
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 417) (codeMat 419) (codeMat 8) = codeMat 64 := by
      unfold actionA; rw [step113_415s11_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 8 * (codeMat 183 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 6 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 6 (by decide)
    have hact : actionA (codeMat 417) (codeMat 419) (codeMat 6) = codeMat 4 := by
      unfold actionA; rw [step113_415s11_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 6 * (codeMat 183 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 5 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 5 (by decide)
    have hact : actionA (codeMat 417) (codeMat 419) (codeMat 5) = codeMat 2 := by
      unfold actionA; rw [step113_415s11_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 5 * (codeMat 183 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 417) (codeMat 419) (codeMat 1) = codeMat 1 := by
      unfold actionA; rw [step113_415s11_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 1 * (codeMat 183 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row11_qr : QuotientRankAtLeast step113_415ActualSource11 11 := by
  have hP : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 419 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 417) (codeMat 419) o25W_wc) 11 :=
    @quotientRankAtLeast_action (codeMat 417) (codeMat 419) hP hQ o25W_wc 11 QiushiMatmul.step109_orbit25_lb11_wc
  exact quotientRankAtLeast_mono step113_415s11_source_le hAct

-- Source 12: row 654, orbit 25, lb 11, cap 5
def step113_415ActualSource12 : Submodule F2 Mat3 := spanCodes [272, 184, 80, 4, 2, 1]

theorem step113_415_row12_W_le_source : o415W ≤ step113_415ActualSource12 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource12
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 184, 80, 4, 2, 1] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 184, 80, 4, 2, 1] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 184, 80, 4, 2, 1] 2 (by decide)

private theorem step113_415s12_QtInv :
    (codeMat 491 : Mat3).transpose⁻¹ = (codeMat 375 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 491 : Mat3).transpose * (codeMat 375 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s12_source_le :
    step113_415ActualSource12 ≤ actionW (codeMat 417) (codeMat 491) o25W_wc := by
  apply step113_415_spanCodes_le_of_gens [272, 184, 80, 4, 2, 1]
    (actionW (codeMat 417) (codeMat 491) o25W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 344 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 344 (by decide)
    have hact : actionA (codeMat 417) (codeMat 491) (codeMat 344) = codeMat 272 := by
      unfold actionA; rw [step113_415s12_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 344 * (codeMat 375 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 264 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 264 (by decide)
    have hact : actionA (codeMat 417) (codeMat 491) (codeMat 264) = codeMat 184 := by
      unfold actionA; rw [step113_415s12_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 264 * (codeMat 375 : Mat3).transpose = codeMat 184
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 336 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 336 (by decide)
    have hact : actionA (codeMat 417) (codeMat 491) (codeMat 336) = codeMat 80 := by
      unfold actionA; rw [step113_415s12_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 336 * (codeMat 375 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 6 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 6 (by decide)
    have hact : actionA (codeMat 417) (codeMat 491) (codeMat 6) = codeMat 4 := by
      unfold actionA; rw [step113_415s12_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 6 * (codeMat 375 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 5 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 5 (by decide)
    have hact : actionA (codeMat 417) (codeMat 491) (codeMat 5) = codeMat 2 := by
      unfold actionA; rw [step113_415s12_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 5 * (codeMat 375 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 7 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 7 (by decide)
    have hact : actionA (codeMat 417) (codeMat 491) (codeMat 7) = codeMat 1 := by
      unfold actionA; rw [step113_415s12_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 7 * (codeMat 375 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row12_qr : QuotientRankAtLeast step113_415ActualSource12 11 := by
  have hP : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 491 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 417) (codeMat 491) o25W_wc) 11 :=
    @quotientRankAtLeast_action (codeMat 417) (codeMat 491) hP hQ o25W_wc 11 QiushiMatmul.step109_orbit25_lb11_wc
  exact quotientRankAtLeast_mono step113_415s12_source_le hAct

-- Source 13: row 664, orbit 25, lb 11, cap 5
def step113_415ActualSource13 : Submodule F2 Mat3 := spanCodes [272, 216, 40, 4, 2, 1]

theorem step113_415_row13_W_le_source : o415W ≤ step113_415ActualSource13 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource13
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 216, 40, 4, 2, 1] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 216, 40, 4, 2, 1] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 216, 40, 4, 2, 1] 2 (by decide)

private theorem step113_415s13_QtInv :
    (codeMat 250 : Mat3).transpose⁻¹ = (codeMat 397 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 250 : Mat3).transpose * (codeMat 397 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s13_source_le :
    step113_415ActualSource13 ≤ actionW (codeMat 177) (codeMat 250) o25W_wc := by
  apply step113_415_spanCodes_le_of_gens [272, 216, 40, 4, 2, 1]
    (actionW (codeMat 177) (codeMat 250) o25W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 336 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 336 (by decide)
    have hact : actionA (codeMat 177) (codeMat 250) (codeMat 336) = codeMat 272 := by
      unfold actionA; rw [step113_415s13_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 336 * (codeMat 397 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 8 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 177) (codeMat 250) (codeMat 8) = codeMat 216 := by
      unfold actionA; rw [step113_415s13_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 8 * (codeMat 397 : Mat3).transpose = codeMat 216
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 256 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 177) (codeMat 250) (codeMat 256) = codeMat 40 := by
      unfold actionA; rw [step113_415s13_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 256 * (codeMat 397 : Mat3).transpose = codeMat 40
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 177) (codeMat 250) (codeMat 2) = codeMat 4 := by
      unfold actionA; rw [step113_415s13_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 2 * (codeMat 397 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 7 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 7 (by decide)
    have hact : actionA (codeMat 177) (codeMat 250) (codeMat 7) = codeMat 2 := by
      unfold actionA; rw [step113_415s13_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 7 * (codeMat 397 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 6 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 6 (by decide)
    have hact : actionA (codeMat 177) (codeMat 250) (codeMat 6) = codeMat 1 := by
      unfold actionA; rw [step113_415s13_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 6 * (codeMat 397 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row13_qr : QuotientRankAtLeast step113_415ActualSource13 11 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 250 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 250) o25W_wc) 11 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 250) hP hQ o25W_wc 11 QiushiMatmul.step109_orbit25_lb11_wc
  exact quotientRankAtLeast_mono step113_415s13_source_le hAct

-- Source 14: row 673, orbit 25, lb 11, cap 5
def step113_415ActualSource14 : Submodule F2 Mat3 := spanCodes [272, 192, 56, 4, 2, 1]

theorem step113_415_row14_W_le_source : o415W ≤ step113_415ActualSource14 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource14
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 192, 56, 4, 2, 1] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 192, 56, 4, 2, 1] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 192, 56, 4, 2, 1] 2 (by decide)

private theorem step113_415s14_QtInv :
    (codeMat 348 : Mat3).transpose⁻¹ = (codeMat 125 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 348 : Mat3).transpose * (codeMat 125 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s14_source_le :
    step113_415ActualSource14 ≤ actionW (codeMat 273) (codeMat 348) o25W_wc := by
  apply step113_415_spanCodes_le_of_gens [272, 192, 56, 4, 2, 1]
    (actionW (codeMat 273) (codeMat 348) o25W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 336 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 336 (by decide)
    have hact : actionA (codeMat 273) (codeMat 348) (codeMat 336) = codeMat 272 := by
      unfold actionA; rw [step113_415s14_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 336 * (codeMat 125 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 256 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 273) (codeMat 348) (codeMat 256) = codeMat 192 := by
      unfold actionA; rw [step113_415s14_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 256 * (codeMat 125 : Mat3).transpose = codeMat 192
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 348) (codeMat 8) = codeMat 56 := by
      unfold actionA; rw [step113_415s14_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 125 : Mat3).transpose = codeMat 56
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 5 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 5 (by decide)
    have hact : actionA (codeMat 273) (codeMat 348) (codeMat 5) = codeMat 4 := by
      unfold actionA; rw [step113_415s14_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 5 * (codeMat 125 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 348) (codeMat 2) = codeMat 2 := by
      unfold actionA; rw [step113_415s14_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 125 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 6 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 6 (by decide)
    have hact : actionA (codeMat 273) (codeMat 348) (codeMat 6) = codeMat 1 := by
      unfold actionA; rw [step113_415s14_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 6 * (codeMat 125 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row14_qr : QuotientRankAtLeast step113_415ActualSource14 11 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 348 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 348) o25W_wc) 11 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 348) hP hQ o25W_wc 11 QiushiMatmul.step109_orbit25_lb11_wc
  exact quotientRankAtLeast_mono step113_415s14_source_le hAct

-- Source 15: row 726, orbit 29, lb 15, cap 1
def step113_415ActualSource15 : Submodule F2 Mat3 := spanCodes [257, 137, 32, 16, 4, 2]

theorem step113_415_row15_W_le_source : o415W ≤ step113_415ActualSource15 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource15
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [257, 137, 32, 16, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [257, 137, 32, 16, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [257, 137, 32, 16, 4, 2] 2 (by decide)

private theorem step113_415s15_QtInv :
    (codeMat 114 : Mat3).transpose⁻¹ = (codeMat 204 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 114 : Mat3).transpose * (codeMat 204 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s15_source_le :
    step113_415ActualSource15 ≤ actionW (codeMat 266) (codeMat 114) orbit29W := by
  apply step113_415_spanCodes_le_of_gens [257, 137, 32, 16, 4, 2]
    (actionW (codeMat 266) (codeMat 114) orbit29W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 160 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 160 (by decide)
    have hact : actionA (codeMat 266) (codeMat 114) (codeMat 160) = codeMat 257 := by
      unfold actionA; rw [step113_415s15_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 160 * (codeMat 204 : Mat3).transpose = codeMat 257
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 228 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 228 (by decide)
    have hact : actionA (codeMat 266) (codeMat 114) (codeMat 228) = codeMat 137 := by
      unfold actionA; rw [step113_415s15_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 228 * (codeMat 204 : Mat3).transpose = codeMat 137
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 114) (codeMat 2) = codeMat 32 := by
      unfold actionA; rw [step113_415s15_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 204 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 3 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 3 (by decide)
    have hact : actionA (codeMat 266) (codeMat 114) (codeMat 3) = codeMat 16 := by
      unfold actionA; rw [step113_415s15_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 3 * (codeMat 204 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 16 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 114) (codeMat 16) = codeMat 4 := by
      unfold actionA; rw [step113_415s15_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 204 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 24 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 24 (by decide)
    have hact : actionA (codeMat 266) (codeMat 114) (codeMat 24) = codeMat 2 := by
      unfold actionA; rw [step113_415s15_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 24 * (codeMat 204 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row15_qr : QuotientRankAtLeast step113_415ActualSource15 15 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 114 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 114) orbit29W) 15 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 114) hP hQ orbit29W 15 QiushiMatmul.orbit29_lb15
  exact quotientRankAtLeast_mono step113_415s15_source_le hAct

-- Source 16: row 727, orbit 29, lb 15, cap 1
def step113_415ActualSource16 : Submodule F2 Mat3 := spanCodes [256, 128, 97, 17, 4, 2]

theorem step113_415_row16_W_le_source : o415W ≤ step113_415ActualSource16 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource16
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 97, 17, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 97, 17, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 97, 17, 4, 2] 2 (by decide)

private theorem step113_415s16_QtInv :
    (codeMat 116 : Mat3).transpose⁻¹ = (codeMat 92 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 116 : Mat3).transpose * (codeMat 92 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s16_source_le :
    step113_415ActualSource16 ≤ actionW (codeMat 140) (codeMat 116) orbit29W := by
  apply step113_415_spanCodes_le_of_gens [256, 128, 97, 17, 4, 2]
    (actionW (codeMat 140) (codeMat 116) orbit29W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 3 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 3 (by decide)
    have hact : actionA (codeMat 140) (codeMat 116) (codeMat 3) = codeMat 256 := by
      unfold actionA; rw [step113_415s16_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 3 * (codeMat 92 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 2 (by decide)
    have hact : actionA (codeMat 140) (codeMat 116) (codeMat 2) = codeMat 128 := by
      unfold actionA; rw [step113_415s16_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 2 * (codeMat 92 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 228 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 228 (by decide)
    have hact : actionA (codeMat 140) (codeMat 116) (codeMat 228) = codeMat 97 := by
      unfold actionA; rw [step113_415s16_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 228 * (codeMat 92 : Mat3).transpose = codeMat 97
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 160 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 160 (by decide)
    have hact : actionA (codeMat 140) (codeMat 116) (codeMat 160) = codeMat 17 := by
      unfold actionA; rw [step113_415s16_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 160 * (codeMat 92 : Mat3).transpose = codeMat 17
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 24 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 24 (by decide)
    have hact : actionA (codeMat 140) (codeMat 116) (codeMat 24) = codeMat 4 := by
      unfold actionA; rw [step113_415s16_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 24 * (codeMat 92 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 16 (by decide)
    have hact : actionA (codeMat 140) (codeMat 116) (codeMat 16) = codeMat 2 := by
      unfold actionA; rw [step113_415s16_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 16 * (codeMat 92 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row16_qr : QuotientRankAtLeast step113_415ActualSource16 15 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 116 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 116) orbit29W) 15 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 116) hP hQ orbit29W 15 QiushiMatmul.orbit29_lb15
  exact quotientRankAtLeast_mono step113_415s16_source_le hAct

-- Source 17: row 730, orbit 29, lb 15, cap 1
def step113_415ActualSource17 : Submodule F2 Mat3 := spanCodes [273, 144, 88, 49, 4, 2]

theorem step113_415_row17_W_le_source : o415W ≤ step113_415ActualSource17 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource17
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 144, 88, 49, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 144, 88, 49, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 144, 88, 49, 4, 2] 2 (by decide)

private theorem step113_415s17_QtInv :
    (codeMat 102 : Mat3).transpose⁻¹ = (codeMat 156 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 102 : Mat3).transpose * (codeMat 156 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s17_source_le :
    step113_415ActualSource17 ≤ actionW (codeMat 142) (codeMat 102) orbit29W := by
  apply step113_415_spanCodes_le_of_gens [273, 144, 88, 49, 4, 2]
    (actionW (codeMat 142) (codeMat 102) orbit29W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 163 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 163 (by decide)
    have hact : actionA (codeMat 142) (codeMat 102) (codeMat 163) = codeMat 273 := by
      unfold actionA; rw [step113_415s17_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 163 * (codeMat 156 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 1 (by decide)
    have hact : actionA (codeMat 142) (codeMat 102) (codeMat 1) = codeMat 144 := by
      unfold actionA; rw [step113_415s17_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 1 * (codeMat 156 : Mat3).transpose = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 68 (by decide)
    have hact : actionA (codeMat 142) (codeMat 102) (codeMat 68) = codeMat 88 := by
      unfold actionA; rw [step113_415s17_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 68 * (codeMat 156 : Mat3).transpose = codeMat 88
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 160 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 160 (by decide)
    have hact : actionA (codeMat 142) (codeMat 102) (codeMat 160) = codeMat 49 := by
      unfold actionA; rw [step113_415s17_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 160 * (codeMat 156 : Mat3).transpose = codeMat 49
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 24 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 24 (by decide)
    have hact : actionA (codeMat 142) (codeMat 102) (codeMat 24) = codeMat 4 := by
      unfold actionA; rw [step113_415s17_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 24 * (codeMat 156 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 8 (by decide)
    have hact : actionA (codeMat 142) (codeMat 102) (codeMat 8) = codeMat 2 := by
      unfold actionA; rw [step113_415s17_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 8 * (codeMat 156 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row17_qr : QuotientRankAtLeast step113_415ActualSource17 15 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 102 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 102) orbit29W) 15 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 102) hP hQ orbit29W 15 QiushiMatmul.orbit29_lb15
  exact quotientRankAtLeast_mono step113_415s17_source_le hAct

-- Source 18: row 769, orbit 35, lb 15, cap 1
def step113_415ActualSource18 : Submodule F2 Mat3 := spanCodes [257, 136, 40, 16, 4, 2]

theorem step113_415_row18_W_le_source : o415W ≤ step113_415ActualSource18 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource18
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [257, 136, 40, 16, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [257, 136, 40, 16, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [257, 136, 40, 16, 4, 2] 2 (by decide)

private theorem step113_415s18_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s18_source_le :
    step113_415ActualSource18 ≤ transposeW (actionW (codeMat 354) (codeMat 273) orbit35W) := by
  apply step113_415_spanCodes_le_of_gens [257, 136, 40, 16, 4, 2]
    (transposeW (actionW (codeMat 354) (codeMat 273) orbit35W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 104 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 104 (by decide)
    have hact : actionA (codeMat 354) (codeMat 273) (codeMat 104) = codeMat 257 := by
      unfold actionA; rw [step113_415s18_QtInv]
      show (codeMat 354 : Mat3).transpose * codeMat 104 * (codeMat 273 : Mat3).transpose = codeMat 257
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 257 ∈ actionW (codeMat 354) (codeMat 273) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 257 : Mat3).transpose = codeMat 257 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h1
    have hw : codeMat 148 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 148 (by decide)
    have hact : actionA (codeMat 354) (codeMat 273) (codeMat 148) = codeMat 34 := by
      unfold actionA; rw [step113_415s18_QtInv]
      show (codeMat 354 : Mat3).transpose * codeMat 148 * (codeMat 273 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 34 ∈ actionW (codeMat 354) (codeMat 273) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 34 : Mat3).transpose = codeMat 136 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h2
    have hw : codeMat 128 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 128 (by decide)
    have hact : actionA (codeMat 354) (codeMat 273) (codeMat 128) = codeMat 130 := by
      unfold actionA; rw [step113_415s18_QtInv]
      show (codeMat 354 : Mat3).transpose * codeMat 128 * (codeMat 273 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 130 ∈ actionW (codeMat 354) (codeMat 273) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 130 : Mat3).transpose = codeMat 40 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h3
    have hw : codeMat 2 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 2 (by decide)
    have hact : actionA (codeMat 354) (codeMat 273) (codeMat 2) = codeMat 16 := by
      unfold actionA; rw [step113_415s18_QtInv]
      show (codeMat 354 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 16 ∈ actionW (codeMat 354) (codeMat 273) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 16 : Mat3).transpose = codeMat 16 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h4
    have hw : codeMat 8 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 8 (by decide)
    have hact : actionA (codeMat 354) (codeMat 273) (codeMat 8) = codeMat 64 := by
      unfold actionA; rw [step113_415s18_QtInv]
      show (codeMat 354 : Mat3).transpose * codeMat 8 * (codeMat 273 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 64 ∈ actionW (codeMat 354) (codeMat 273) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 64 : Mat3).transpose = codeMat 4 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h5
    have hw : codeMat 1 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 1 (by decide)
    have hact : actionA (codeMat 354) (codeMat 273) (codeMat 1) = codeMat 8 := by
      unfold actionA; rw [step113_415s18_QtInv]
      show (codeMat 354 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 8 ∈ actionW (codeMat 354) (codeMat 273) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 8 : Mat3).transpose = codeMat 2 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans

theorem step113_415_row18_qr : QuotientRankAtLeast step113_415ActualSource18 15 := by
  have hP : Invertible (codeMat 354 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 354) (codeMat 273) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 354) (codeMat 273) hP hQ orbit35W 15 QiushiMatmul.orbit35_lb15
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 354) (codeMat 273) orbit35W)) 15 :=
    quotientRankAtLeast_transpose hAct
  exact quotientRankAtLeast_mono step113_415s18_source_le hT

-- Source 19: row 770, orbit 35, lb 15, cap 1
def step113_415ActualSource19 : Submodule F2 Mat3 := spanCodes [257, 137, 41, 16, 4, 2]

theorem step113_415_row19_W_le_source : o415W ≤ step113_415ActualSource19 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource19
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [257, 137, 41, 16, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [257, 137, 41, 16, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [257, 137, 41, 16, 4, 2] 2 (by decide)

private theorem step113_415s19_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = (codeMat 275 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * (codeMat 275 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s19_source_le :
    step113_415ActualSource19 ≤ transposeW (actionW (codeMat 354) (codeMat 275) orbit35W) := by
  apply step113_415_spanCodes_le_of_gens [257, 137, 41, 16, 4, 2]
    (transposeW (actionW (codeMat 354) (codeMat 275) orbit35W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 104 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 104 (by decide)
    have hact : actionA (codeMat 354) (codeMat 275) (codeMat 104) = codeMat 257 := by
      unfold actionA; rw [step113_415s19_QtInv]
      show (codeMat 354 : Mat3).transpose * codeMat 104 * (codeMat 275 : Mat3).transpose = codeMat 257
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 257 ∈ actionW (codeMat 354) (codeMat 275) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 257 : Mat3).transpose = codeMat 257 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h1
    have hw : codeMat 148 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 148 (by decide)
    have hact : actionA (codeMat 354) (codeMat 275) (codeMat 148) = codeMat 35 := by
      unfold actionA; rw [step113_415s19_QtInv]
      show (codeMat 354 : Mat3).transpose * codeMat 148 * (codeMat 275 : Mat3).transpose = codeMat 35
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 35 ∈ actionW (codeMat 354) (codeMat 275) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 35 : Mat3).transpose = codeMat 137 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h2
    have hw : codeMat 136 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 136 (by decide)
    have hact : actionA (codeMat 354) (codeMat 275) (codeMat 136) = codeMat 131 := by
      unfold actionA; rw [step113_415s19_QtInv]
      show (codeMat 354 : Mat3).transpose * codeMat 136 * (codeMat 275 : Mat3).transpose = codeMat 131
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 131 ∈ actionW (codeMat 354) (codeMat 275) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 131 : Mat3).transpose = codeMat 41 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h3
    have hw : codeMat 3 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 3 (by decide)
    have hact : actionA (codeMat 354) (codeMat 275) (codeMat 3) = codeMat 16 := by
      unfold actionA; rw [step113_415s19_QtInv]
      show (codeMat 354 : Mat3).transpose * codeMat 3 * (codeMat 275 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 16 ∈ actionW (codeMat 354) (codeMat 275) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 16 : Mat3).transpose = codeMat 16 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h4
    have hw : codeMat 8 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 8 (by decide)
    have hact : actionA (codeMat 354) (codeMat 275) (codeMat 8) = codeMat 64 := by
      unfold actionA; rw [step113_415s19_QtInv]
      show (codeMat 354 : Mat3).transpose * codeMat 8 * (codeMat 275 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 64 ∈ actionW (codeMat 354) (codeMat 275) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 64 : Mat3).transpose = codeMat 4 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h5
    have hw : codeMat 1 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 1 (by decide)
    have hact : actionA (codeMat 354) (codeMat 275) (codeMat 1) = codeMat 8 := by
      unfold actionA; rw [step113_415s19_QtInv]
      show (codeMat 354 : Mat3).transpose * codeMat 1 * (codeMat 275 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 8 ∈ actionW (codeMat 354) (codeMat 275) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 8 : Mat3).transpose = codeMat 2 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans

theorem step113_415_row19_qr : QuotientRankAtLeast step113_415ActualSource19 15 := by
  have hP : Invertible (codeMat 354 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 354) (codeMat 275) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 354) (codeMat 275) hP hQ orbit35W 15 QiushiMatmul.orbit35_lb15
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 354) (codeMat 275) orbit35W)) 15 :=
    quotientRankAtLeast_transpose hAct
  exact quotientRankAtLeast_mono step113_415s19_source_le hT

-- Source 20: row 771, orbit 35, lb 15, cap 1
def step113_415ActualSource20 : Submodule F2 Mat3 := spanCodes [264, 129, 41, 25, 4, 2]

theorem step113_415_row20_W_le_source : o415W ≤ step113_415ActualSource20 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource20
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [264, 129, 41, 25, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [264, 129, 41, 25, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [264, 129, 41, 25, 4, 2] 2 (by decide)

private theorem step113_415s20_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = (codeMat 275 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * (codeMat 275 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s20_source_le :
    step113_415ActualSource20 ≤ transposeW (actionW (codeMat 214) (codeMat 275) orbit35W) := by
  apply step113_415_spanCodes_le_of_gens [264, 129, 41, 25, 4, 2]
    (transposeW (actionW (codeMat 214) (codeMat 275) orbit35W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 252 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 252 (by decide)
    have hact : actionA (codeMat 214) (codeMat 275) (codeMat 252) = codeMat 258 := by
      unfold actionA; rw [step113_415s20_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 252 * (codeMat 275 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 258 ∈ actionW (codeMat 214) (codeMat 275) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 258 : Mat3).transpose = codeMat 264 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h1
    have hw : codeMat 104 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 104 (by decide)
    have hact : actionA (codeMat 214) (codeMat 275) (codeMat 104) = codeMat 33 := by
      unfold actionA; rw [step113_415s20_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 104 * (codeMat 275 : Mat3).transpose = codeMat 33
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 33 ∈ actionW (codeMat 214) (codeMat 275) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 33 : Mat3).transpose = codeMat 129 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h2
    have hw : codeMat 139 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 139 (by decide)
    have hact : actionA (codeMat 214) (codeMat 275) (codeMat 139) = codeMat 131 := by
      unfold actionA; rw [step113_415s20_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 139 * (codeMat 275 : Mat3).transpose = codeMat 131
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 131 ∈ actionW (codeMat 214) (codeMat 275) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 131 : Mat3).transpose = codeMat 41 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h3
    have hw : codeMat 136 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 136 (by decide)
    have hact : actionA (codeMat 214) (codeMat 275) (codeMat 136) = codeMat 19 := by
      unfold actionA; rw [step113_415s20_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 136 * (codeMat 275 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 19 ∈ actionW (codeMat 214) (codeMat 275) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 19 : Mat3).transpose = codeMat 25 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h4
    have hw : codeMat 9 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 9 (by decide)
    have hact : actionA (codeMat 214) (codeMat 275) (codeMat 9) = codeMat 64 := by
      unfold actionA; rw [step113_415s20_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 9 * (codeMat 275 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 64 ∈ actionW (codeMat 214) (codeMat 275) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 64 : Mat3).transpose = codeMat 4 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h5
    have hw : codeMat 8 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 8 (by decide)
    have hact : actionA (codeMat 214) (codeMat 275) (codeMat 8) = codeMat 8 := by
      unfold actionA; rw [step113_415s20_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 8 * (codeMat 275 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 8 ∈ actionW (codeMat 214) (codeMat 275) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 8 : Mat3).transpose = codeMat 2 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans

theorem step113_415_row20_qr : QuotientRankAtLeast step113_415ActualSource20 15 := by
  have hP : Invertible (codeMat 214 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 214) (codeMat 275) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 214) (codeMat 275) hP hQ orbit35W 15 QiushiMatmul.orbit35_lb15
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 214) (codeMat 275) orbit35W)) 15 :=
    quotientRankAtLeast_transpose hAct
  exact quotientRankAtLeast_mono step113_415s20_source_le hT

-- Source 21: row 772, orbit 35, lb 15, cap 1
def step113_415ActualSource21 : Submodule F2 Mat3 := spanCodes [265, 129, 40, 24, 4, 2]

theorem step113_415_row21_W_le_source : o415W ≤ step113_415ActualSource21 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource21
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [265, 129, 40, 24, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [265, 129, 40, 24, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [265, 129, 40, 24, 4, 2] 2 (by decide)

private theorem step113_415s21_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s21_source_le :
    step113_415ActualSource21 ≤ transposeW (actionW (codeMat 214) (codeMat 273) orbit35W) := by
  apply step113_415_spanCodes_le_of_gens [265, 129, 40, 24, 4, 2]
    (transposeW (actionW (codeMat 214) (codeMat 273) orbit35W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 252 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 252 (by decide)
    have hact : actionA (codeMat 214) (codeMat 273) (codeMat 252) = codeMat 259 := by
      unfold actionA; rw [step113_415s21_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 252 * (codeMat 273 : Mat3).transpose = codeMat 259
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 259 ∈ actionW (codeMat 214) (codeMat 273) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 259 : Mat3).transpose = codeMat 265 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h1
    have hw : codeMat 104 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 104 (by decide)
    have hact : actionA (codeMat 214) (codeMat 273) (codeMat 104) = codeMat 33 := by
      unfold actionA; rw [step113_415s21_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 104 * (codeMat 273 : Mat3).transpose = codeMat 33
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 33 ∈ actionW (codeMat 214) (codeMat 273) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 33 : Mat3).transpose = codeMat 129 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h2
    have hw : codeMat 130 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 130 (by decide)
    have hact : actionA (codeMat 214) (codeMat 273) (codeMat 130) = codeMat 130 := by
      unfold actionA; rw [step113_415s21_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 130 * (codeMat 273 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 130 ∈ actionW (codeMat 214) (codeMat 273) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 130 : Mat3).transpose = codeMat 40 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h3
    have hw : codeMat 128 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 128 (by decide)
    have hact : actionA (codeMat 214) (codeMat 273) (codeMat 128) = codeMat 18 := by
      unfold actionA; rw [step113_415s21_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 128 * (codeMat 273 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 18 ∈ actionW (codeMat 214) (codeMat 273) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 18 : Mat3).transpose = codeMat 24 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h4
    have hw : codeMat 9 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 9 (by decide)
    have hact : actionA (codeMat 214) (codeMat 273) (codeMat 9) = codeMat 64 := by
      unfold actionA; rw [step113_415s21_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 9 * (codeMat 273 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 64 ∈ actionW (codeMat 214) (codeMat 273) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 64 : Mat3).transpose = codeMat 4 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h5
    have hw : codeMat 8 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 8 (by decide)
    have hact : actionA (codeMat 214) (codeMat 273) (codeMat 8) = codeMat 8 := by
      unfold actionA; rw [step113_415s21_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 8 * (codeMat 273 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 8 ∈ actionW (codeMat 214) (codeMat 273) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 8 : Mat3).transpose = codeMat 2 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans

theorem step113_415_row21_qr : QuotientRankAtLeast step113_415ActualSource21 15 := by
  have hP : Invertible (codeMat 214 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 214) (codeMat 273) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 214) (codeMat 273) hP hQ orbit35W 15 QiushiMatmul.orbit35_lb15
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 214) (codeMat 273) orbit35W)) 15 :=
    quotientRankAtLeast_transpose hAct
  exact quotientRankAtLeast_mono step113_415s21_source_le hT

-- Source 22: row 775, orbit 35, lb 15, cap 1
def step113_415ActualSource22 : Submodule F2 Mat3 := spanCodes [257, 160, 16, 8, 4, 2]

theorem step113_415_row22_W_le_source : o415W ≤ step113_415ActualSource22 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource22
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [257, 160, 16, 8, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [257, 160, 16, 8, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [257, 160, 16, 8, 4, 2] 2 (by decide)

private theorem step113_415s22_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s22_source_le :
    step113_415ActualSource22 ≤ transposeW (actionW (codeMat 98) (codeMat 273) orbit35W) := by
  apply step113_415_spanCodes_le_of_gens [257, 160, 16, 8, 4, 2]
    (transposeW (actionW (codeMat 98) (codeMat 273) orbit35W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 96 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 96 (by decide)
    have hact : actionA (codeMat 98) (codeMat 273) (codeMat 96) = codeMat 257 := by
      unfold actionA; rw [step113_415s22_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 96 * (codeMat 273 : Mat3).transpose = codeMat 257
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 257 ∈ actionW (codeMat 98) (codeMat 273) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 257 : Mat3).transpose = codeMat 257 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h1
    have hw : codeMat 20 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 20 (by decide)
    have hact : actionA (codeMat 98) (codeMat 273) (codeMat 20) = codeMat 160 := by
      unfold actionA; rw [step113_415s22_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 20 * (codeMat 273 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 160 ∈ actionW (codeMat 98) (codeMat 273) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 160 : Mat3).transpose = codeMat 160 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h2
    have hw : codeMat 2 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 2 (by decide)
    have hact : actionA (codeMat 98) (codeMat 273) (codeMat 2) = codeMat 16 := by
      unfold actionA; rw [step113_415s22_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 16 ∈ actionW (codeMat 98) (codeMat 273) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 16 : Mat3).transpose = codeMat 16 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h3
    have hw : codeMat 128 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 128 (by decide)
    have hact : actionA (codeMat 98) (codeMat 273) (codeMat 128) = codeMat 2 := by
      unfold actionA; rw [step113_415s22_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 128 * (codeMat 273 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 2 ∈ actionW (codeMat 98) (codeMat 273) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 2 : Mat3).transpose = codeMat 8 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h4
    have hw : codeMat 8 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 8 (by decide)
    have hact : actionA (codeMat 98) (codeMat 273) (codeMat 8) = codeMat 64 := by
      unfold actionA; rw [step113_415s22_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 8 * (codeMat 273 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 64 ∈ actionW (codeMat 98) (codeMat 273) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 64 : Mat3).transpose = codeMat 4 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h5
    have hw : codeMat 1 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 1 (by decide)
    have hact : actionA (codeMat 98) (codeMat 273) (codeMat 1) = codeMat 8 := by
      unfold actionA; rw [step113_415s22_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 8 ∈ actionW (codeMat 98) (codeMat 273) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 8 : Mat3).transpose = codeMat 2 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans

theorem step113_415_row22_qr : QuotientRankAtLeast step113_415ActualSource22 15 := by
  have hP : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 98) (codeMat 273) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 98) (codeMat 273) hP hQ orbit35W 15 QiushiMatmul.orbit35_lb15
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 98) (codeMat 273) orbit35W)) 15 :=
    quotientRankAtLeast_transpose hAct
  exact quotientRankAtLeast_mono step113_415s22_source_le hT

-- Source 23: row 776, orbit 35, lb 15, cap 1
def step113_415ActualSource23 : Submodule F2 Mat3 := spanCodes [273, 129, 48, 9, 4, 2]

theorem step113_415_row23_W_le_source : o415W ≤ step113_415ActualSource23 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource23
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 129, 48, 9, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 129, 48, 9, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 129, 48, 9, 4, 2] 2 (by decide)

private theorem step113_415s23_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = (codeMat 275 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * (codeMat 275 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s23_source_le :
    step113_415ActualSource23 ≤ transposeW (actionW (codeMat 86) (codeMat 275) orbit35W) := by
  apply step113_415_spanCodes_le_of_gens [273, 129, 48, 9, 4, 2]
    (transposeW (actionW (codeMat 86) (codeMat 275) orbit35W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 124 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 124 (by decide)
    have hact : actionA (codeMat 86) (codeMat 275) (codeMat 124) = codeMat 273 := by
      unfold actionA; rw [step113_415s23_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 124 * (codeMat 275 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 273 ∈ actionW (codeMat 86) (codeMat 275) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 273 : Mat3).transpose = codeMat 273 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h1
    have hw : codeMat 96 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 96 (by decide)
    have hact : actionA (codeMat 86) (codeMat 275) (codeMat 96) = codeMat 33 := by
      unfold actionA; rw [step113_415s23_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 96 * (codeMat 275 : Mat3).transpose = codeMat 33
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 33 ∈ actionW (codeMat 86) (codeMat 275) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 33 : Mat3).transpose = codeMat 129 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h2
    have hw : codeMat 3 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 3 (by decide)
    have hact : actionA (codeMat 86) (codeMat 275) (codeMat 3) = codeMat 144 := by
      unfold actionA; rw [step113_415s23_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 3 * (codeMat 275 : Mat3).transpose = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 144 ∈ actionW (codeMat 86) (codeMat 275) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 144 : Mat3).transpose = codeMat 48 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h3
    have hw : codeMat 128 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 128 (by decide)
    have hact : actionA (codeMat 86) (codeMat 275) (codeMat 128) = codeMat 3 := by
      unfold actionA; rw [step113_415s23_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 128 * (codeMat 275 : Mat3).transpose = codeMat 3
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 3 ∈ actionW (codeMat 86) (codeMat 275) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 3 : Mat3).transpose = codeMat 9 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h4
    have hw : codeMat 9 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 9 (by decide)
    have hact : actionA (codeMat 86) (codeMat 275) (codeMat 9) = codeMat 64 := by
      unfold actionA; rw [step113_415s23_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 9 * (codeMat 275 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 64 ∈ actionW (codeMat 86) (codeMat 275) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 64 : Mat3).transpose = codeMat 4 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h5
    have hw : codeMat 8 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 8 (by decide)
    have hact : actionA (codeMat 86) (codeMat 275) (codeMat 8) = codeMat 8 := by
      unfold actionA; rw [step113_415s23_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 8 * (codeMat 275 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 8 ∈ actionW (codeMat 86) (codeMat 275) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 8 : Mat3).transpose = codeMat 2 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans

theorem step113_415_row23_qr : QuotientRankAtLeast step113_415ActualSource23 15 := by
  have hP : Invertible (codeMat 86 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 86) (codeMat 275) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 86) (codeMat 275) hP hQ orbit35W 15 QiushiMatmul.orbit35_lb15
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 86) (codeMat 275) orbit35W)) 15 :=
    quotientRankAtLeast_transpose hAct
  exact quotientRankAtLeast_mono step113_415s23_source_le hT

-- Source 24: row 779, orbit 35, lb 15, cap 1
def step113_415ActualSource24 : Submodule F2 Mat3 := spanCodes [257, 160, 16, 9, 4, 2]

theorem step113_415_row24_W_le_source : o415W ≤ step113_415ActualSource24 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource24
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [257, 160, 16, 9, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [257, 160, 16, 9, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [257, 160, 16, 9, 4, 2] 2 (by decide)

private theorem step113_415s24_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = (codeMat 275 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * (codeMat 275 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s24_source_le :
    step113_415ActualSource24 ≤ transposeW (actionW (codeMat 98) (codeMat 275) orbit35W) := by
  apply step113_415_spanCodes_le_of_gens [257, 160, 16, 9, 4, 2]
    (transposeW (actionW (codeMat 98) (codeMat 275) orbit35W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 96 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 96 (by decide)
    have hact : actionA (codeMat 98) (codeMat 275) (codeMat 96) = codeMat 257 := by
      unfold actionA; rw [step113_415s24_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 96 * (codeMat 275 : Mat3).transpose = codeMat 257
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 257 ∈ actionW (codeMat 98) (codeMat 275) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 257 : Mat3).transpose = codeMat 257 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h1
    have hw : codeMat 28 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 28 (by decide)
    have hact : actionA (codeMat 98) (codeMat 275) (codeMat 28) = codeMat 160 := by
      unfold actionA; rw [step113_415s24_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 28 * (codeMat 275 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 160 ∈ actionW (codeMat 98) (codeMat 275) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 160 : Mat3).transpose = codeMat 160 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h2
    have hw : codeMat 3 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 3 (by decide)
    have hact : actionA (codeMat 98) (codeMat 275) (codeMat 3) = codeMat 16 := by
      unfold actionA; rw [step113_415s24_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 3 * (codeMat 275 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 16 ∈ actionW (codeMat 98) (codeMat 275) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 16 : Mat3).transpose = codeMat 16 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h3
    have hw : codeMat 128 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 128 (by decide)
    have hact : actionA (codeMat 98) (codeMat 275) (codeMat 128) = codeMat 3 := by
      unfold actionA; rw [step113_415s24_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 128 * (codeMat 275 : Mat3).transpose = codeMat 3
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 3 ∈ actionW (codeMat 98) (codeMat 275) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 3 : Mat3).transpose = codeMat 9 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h4
    have hw : codeMat 8 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 8 (by decide)
    have hact : actionA (codeMat 98) (codeMat 275) (codeMat 8) = codeMat 64 := by
      unfold actionA; rw [step113_415s24_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 8 * (codeMat 275 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 64 ∈ actionW (codeMat 98) (codeMat 275) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 64 : Mat3).transpose = codeMat 4 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h5
    have hw : codeMat 1 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 1 (by decide)
    have hact : actionA (codeMat 98) (codeMat 275) (codeMat 1) = codeMat 8 := by
      unfold actionA; rw [step113_415s24_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 1 * (codeMat 275 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 8 ∈ actionW (codeMat 98) (codeMat 275) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 8 : Mat3).transpose = codeMat 2 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans

theorem step113_415_row24_qr : QuotientRankAtLeast step113_415ActualSource24 15 := by
  have hP : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 98) (codeMat 275) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 98) (codeMat 275) hP hQ orbit35W 15 QiushiMatmul.orbit35_lb15
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 98) (codeMat 275) orbit35W)) 15 :=
    quotientRankAtLeast_transpose hAct
  exact quotientRankAtLeast_mono step113_415s24_source_le hT

-- Source 25: row 780, orbit 35, lb 15, cap 1
def step113_415ActualSource25 : Submodule F2 Mat3 := spanCodes [273, 129, 48, 8, 4, 2]

theorem step113_415_row25_W_le_source : o415W ≤ step113_415ActualSource25 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource25
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 129, 48, 8, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 129, 48, 8, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 129, 48, 8, 4, 2] 2 (by decide)

private theorem step113_415s25_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s25_source_le :
    step113_415ActualSource25 ≤ transposeW (actionW (codeMat 86) (codeMat 273) orbit35W) := by
  apply step113_415_spanCodes_le_of_gens [273, 129, 48, 8, 4, 2]
    (transposeW (actionW (codeMat 86) (codeMat 273) orbit35W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 116 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 116 (by decide)
    have hact : actionA (codeMat 86) (codeMat 273) (codeMat 116) = codeMat 273 := by
      unfold actionA; rw [step113_415s25_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 116 * (codeMat 273 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 273 ∈ actionW (codeMat 86) (codeMat 273) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 273 : Mat3).transpose = codeMat 273 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h1
    have hw : codeMat 96 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 96 (by decide)
    have hact : actionA (codeMat 86) (codeMat 273) (codeMat 96) = codeMat 33 := by
      unfold actionA; rw [step113_415s25_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 96 * (codeMat 273 : Mat3).transpose = codeMat 33
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 33 ∈ actionW (codeMat 86) (codeMat 273) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 33 : Mat3).transpose = codeMat 129 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h2
    have hw : codeMat 2 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 2 (by decide)
    have hact : actionA (codeMat 86) (codeMat 273) (codeMat 2) = codeMat 144 := by
      unfold actionA; rw [step113_415s25_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 144 ∈ actionW (codeMat 86) (codeMat 273) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 144 : Mat3).transpose = codeMat 48 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h3
    have hw : codeMat 128 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 128 (by decide)
    have hact : actionA (codeMat 86) (codeMat 273) (codeMat 128) = codeMat 2 := by
      unfold actionA; rw [step113_415s25_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 128 * (codeMat 273 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 2 ∈ actionW (codeMat 86) (codeMat 273) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 2 : Mat3).transpose = codeMat 8 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h4
    have hw : codeMat 9 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 9 (by decide)
    have hact : actionA (codeMat 86) (codeMat 273) (codeMat 9) = codeMat 64 := by
      unfold actionA; rw [step113_415s25_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 9 * (codeMat 273 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 64 ∈ actionW (codeMat 86) (codeMat 273) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 64 : Mat3).transpose = codeMat 4 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h5
    have hw : codeMat 8 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 8 (by decide)
    have hact : actionA (codeMat 86) (codeMat 273) (codeMat 8) = codeMat 8 := by
      unfold actionA; rw [step113_415s25_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 8 * (codeMat 273 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 8 ∈ actionW (codeMat 86) (codeMat 273) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 8 : Mat3).transpose = codeMat 2 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans

theorem step113_415_row25_qr : QuotientRankAtLeast step113_415ActualSource25 15 := by
  have hP : Invertible (codeMat 86 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 86) (codeMat 273) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 86) (codeMat 273) hP hQ orbit35W 15 QiushiMatmul.orbit35_lb15
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 86) (codeMat 273) orbit35W)) 15 :=
    quotientRankAtLeast_transpose hAct
  exact quotientRankAtLeast_mono step113_415s25_source_le hT

-- Source 26: row 782, orbit 35, lb 15, cap 1
def step113_415ActualSource26 : Submodule F2 Mat3 := spanCodes [256, 160, 96, 17, 4, 2]

theorem step113_415_row26_W_le_source : o415W ≤ step113_415ActualSource26 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource26
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 96, 17, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 96, 17, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 96, 17, 4, 2] 2 (by decide)

private theorem step113_415s26_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s26_source_le :
    step113_415ActualSource26 ≤ transposeW (actionW (codeMat 212) (codeMat 161) orbit35W) := by
  apply step113_415_spanCodes_le_of_gens [256, 160, 96, 17, 4, 2]
    (transposeW (actionW (codeMat 212) (codeMat 161) orbit35W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 2 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 2 (by decide)
    have hact : actionA (codeMat 212) (codeMat 161) (codeMat 2) = codeMat 256 := by
      unfold actionA; rw [step113_415s26_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 2 * (codeMat 161 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 256 ∈ actionW (codeMat 212) (codeMat 161) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 256 : Mat3).transpose = codeMat 256 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h1
    have hw : codeMat 20 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 20 (by decide)
    have hact : actionA (codeMat 212) (codeMat 161) (codeMat 20) = codeMat 160 := by
      unfold actionA; rw [step113_415s26_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 20 * (codeMat 161 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 160 ∈ actionW (codeMat 212) (codeMat 161) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 160 : Mat3).transpose = codeMat 160 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h2
    have hw : codeMat 148 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 148 (by decide)
    have hact : actionA (codeMat 212) (codeMat 161) (codeMat 148) = codeMat 132 := by
      unfold actionA; rw [step113_415s26_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 148 * (codeMat 161 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 132 ∈ actionW (codeMat 212) (codeMat 161) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 132 : Mat3).transpose = codeMat 96 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h3
    have hw : codeMat 104 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 104 (by decide)
    have hact : actionA (codeMat 212) (codeMat 161) (codeMat 104) = codeMat 17 := by
      unfold actionA; rw [step113_415s26_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 104 * (codeMat 161 : Mat3).transpose = codeMat 17
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 17 ∈ actionW (codeMat 212) (codeMat 161) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 17 : Mat3).transpose = codeMat 17 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h4
    have hw : codeMat 1 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 1 (by decide)
    have hact : actionA (codeMat 212) (codeMat 161) (codeMat 1) = codeMat 64 := by
      unfold actionA; rw [step113_415s26_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 64 ∈ actionW (codeMat 212) (codeMat 161) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 64 : Mat3).transpose = codeMat 4 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h5
    have hw : codeMat 8 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 8 (by decide)
    have hact : actionA (codeMat 212) (codeMat 161) (codeMat 8) = codeMat 8 := by
      unfold actionA; rw [step113_415s26_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 8 * (codeMat 161 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 8 ∈ actionW (codeMat 212) (codeMat 161) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 8 : Mat3).transpose = codeMat 2 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans

theorem step113_415_row26_qr : QuotientRankAtLeast step113_415ActualSource26 15 := by
  have hP : Invertible (codeMat 212 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 212) (codeMat 161) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 212) (codeMat 161) hP hQ orbit35W 15 QiushiMatmul.orbit35_lb15
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 212) (codeMat 161) orbit35W)) 15 :=
    quotientRankAtLeast_transpose hAct
  exact quotientRankAtLeast_mono step113_415s26_source_le hT

-- Source 27: row 783, orbit 35, lb 15, cap 1
def step113_415ActualSource27 : Submodule F2 Mat3 := spanCodes [273, 145, 80, 33, 4, 2]

theorem step113_415_row27_W_le_source : o415W ≤ step113_415ActualSource27 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource27
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 145, 80, 33, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 145, 80, 33, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 145, 80, 33, 4, 2] 2 (by decide)

private theorem step113_415s27_QtInv :
    (codeMat 181 : Mat3).transpose⁻¹ = (codeMat 423 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 181 : Mat3).transpose * (codeMat 423 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s27_source_le :
    step113_415ActualSource27 ≤ transposeW (actionW (codeMat 214) (codeMat 181) orbit35W) := by
  apply step113_415_spanCodes_le_of_gens [273, 145, 80, 33, 4, 2]
    (transposeW (actionW (codeMat 214) (codeMat 181) orbit35W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 99 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 99 (by decide)
    have hact : actionA (codeMat 214) (codeMat 181) (codeMat 99) = codeMat 273 := by
      unfold actionA; rw [step113_415s27_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 99 * (codeMat 423 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 273 ∈ actionW (codeMat 214) (codeMat 181) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 273 : Mat3).transpose = codeMat 273 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h1
    have hw : codeMat 96 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 96 (by decide)
    have hact : actionA (codeMat 214) (codeMat 181) (codeMat 96) = codeMat 49 := by
      unfold actionA; rw [step113_415s27_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 96 * (codeMat 423 : Mat3).transpose = codeMat 49
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 49 ∈ actionW (codeMat 214) (codeMat 181) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 49 : Mat3).transpose = codeMat 145 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h2
    have hw : codeMat 232 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 232 (by decide)
    have hact : actionA (codeMat 214) (codeMat 181) (codeMat 232) = codeMat 20 := by
      unfold actionA; rw [step113_415s27_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 232 * (codeMat 423 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 20 ∈ actionW (codeMat 214) (codeMat 181) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 20 : Mat3).transpose = codeMat 80 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h3
    have hw : codeMat 126 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 126 (by decide)
    have hact : actionA (codeMat 214) (codeMat 181) (codeMat 126) = codeMat 129 := by
      unfold actionA; rw [step113_415s27_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 126 * (codeMat 423 : Mat3).transpose = codeMat 129
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 129 ∈ actionW (codeMat 214) (codeMat 181) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 129 : Mat3).transpose = codeMat 33 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h4
    have hw : codeMat 9 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 9 (by decide)
    have hact : actionA (codeMat 214) (codeMat 181) (codeMat 9) = codeMat 64 := by
      unfold actionA; rw [step113_415s27_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 9 * (codeMat 423 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 64 ∈ actionW (codeMat 214) (codeMat 181) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 64 : Mat3).transpose = codeMat 4 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h5
    have hw : codeMat 8 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 8 (by decide)
    have hact : actionA (codeMat 214) (codeMat 181) (codeMat 8) = codeMat 8 := by
      unfold actionA; rw [step113_415s27_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 8 * (codeMat 423 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 8 ∈ actionW (codeMat 214) (codeMat 181) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 8 : Mat3).transpose = codeMat 2 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans

theorem step113_415_row27_qr : QuotientRankAtLeast step113_415ActualSource27 15 := by
  have hP : Invertible (codeMat 214 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 181 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 214) (codeMat 181) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 214) (codeMat 181) hP hQ orbit35W 15 QiushiMatmul.orbit35_lb15
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 214) (codeMat 181) orbit35W)) 15 :=
    quotientRankAtLeast_transpose hAct
  exact quotientRankAtLeast_mono step113_415s27_source_le hT

-- Source 28: row 784, orbit 35, lb 15, cap 1
def step113_415ActualSource28 : Submodule F2 Mat3 := spanCodes [273, 145, 81, 33, 4, 2]

theorem step113_415_row28_W_le_source : o415W ≤ step113_415ActualSource28 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource28
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 145, 81, 33, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 145, 81, 33, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 145, 81, 33, 4, 2] 2 (by decide)

private theorem step113_415s28_QtInv :
    (codeMat 177 : Mat3).transpose⁻¹ = (codeMat 417 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 177 : Mat3).transpose * (codeMat 417 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s28_source_le :
    step113_415ActualSource28 ≤ transposeW (actionW (codeMat 214) (codeMat 177) orbit35W) := by
  apply step113_415_spanCodes_le_of_gens [273, 145, 81, 33, 4, 2]
    (transposeW (actionW (codeMat 214) (codeMat 177) orbit35W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 106 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 106 (by decide)
    have hact : actionA (codeMat 214) (codeMat 177) (codeMat 106) = codeMat 273 := by
      unfold actionA; rw [step113_415s28_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 106 * (codeMat 417 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 273 ∈ actionW (codeMat 214) (codeMat 177) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 273 : Mat3).transpose = codeMat 273 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h1
    have hw : codeMat 104 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 104 (by decide)
    have hact : actionA (codeMat 214) (codeMat 177) (codeMat 104) = codeMat 49 := by
      unfold actionA; rw [step113_415s28_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 104 * (codeMat 417 : Mat3).transpose = codeMat 49
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 49 ∈ actionW (codeMat 214) (codeMat 177) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 49 : Mat3).transpose = codeMat 145 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h2
    have hw : codeMat 232 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 232 (by decide)
    have hact : actionA (codeMat 214) (codeMat 177) (codeMat 232) = codeMat 21 := by
      unfold actionA; rw [step113_415s28_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 232 * (codeMat 417 : Mat3).transpose = codeMat 21
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 21 ∈ actionW (codeMat 214) (codeMat 177) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 21 : Mat3).transpose = codeMat 81 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h3
    have hw : codeMat 126 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 126 (by decide)
    have hact : actionA (codeMat 214) (codeMat 177) (codeMat 126) = codeMat 129 := by
      unfold actionA; rw [step113_415s28_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 126 * (codeMat 417 : Mat3).transpose = codeMat 129
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 129 ∈ actionW (codeMat 214) (codeMat 177) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 129 : Mat3).transpose = codeMat 33 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h4
    have hw : codeMat 9 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 9 (by decide)
    have hact : actionA (codeMat 214) (codeMat 177) (codeMat 9) = codeMat 64 := by
      unfold actionA; rw [step113_415s28_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 9 * (codeMat 417 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 64 ∈ actionW (codeMat 214) (codeMat 177) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 64 : Mat3).transpose = codeMat 4 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h5
    have hw : codeMat 8 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 8 (by decide)
    have hact : actionA (codeMat 214) (codeMat 177) (codeMat 8) = codeMat 8 := by
      unfold actionA; rw [step113_415s28_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 8 * (codeMat 417 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 8 ∈ actionW (codeMat 214) (codeMat 177) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 8 : Mat3).transpose = codeMat 2 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans

theorem step113_415_row28_qr : QuotientRankAtLeast step113_415ActualSource28 15 := by
  have hP : Invertible (codeMat 214 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 214) (codeMat 177) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 214) (codeMat 177) hP hQ orbit35W 15 QiushiMatmul.orbit35_lb15
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 214) (codeMat 177) orbit35W)) 15 :=
    quotientRankAtLeast_transpose hAct
  exact quotientRankAtLeast_mono step113_415s28_source_le hT

-- Source 29: row 786, orbit 35, lb 15, cap 1
def step113_415ActualSource29 : Submodule F2 Mat3 := spanCodes [273, 129, 88, 49, 4, 2]

theorem step113_415_row29_W_le_source : o415W ≤ step113_415ActualSource29 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource29
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 129, 88, 49, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 129, 88, 49, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 129, 88, 49, 4, 2] 2 (by decide)

private theorem step113_415s29_QtInv :
    (codeMat 403 : Mat3).transpose⁻¹ = (codeMat 403 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 403 : Mat3).transpose * (codeMat 403 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s29_source_le :
    step113_415ActualSource29 ≤ transposeW (actionW (codeMat 212) (codeMat 403) orbit35W) := by
  apply step113_415_spanCodes_le_of_gens [273, 129, 88, 49, 4, 2]
    (transposeW (actionW (codeMat 212) (codeMat 403) orbit35W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 116 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 116 (by decide)
    have hact : actionA (codeMat 212) (codeMat 403) (codeMat 116) = codeMat 273 := by
      unfold actionA; rw [step113_415s29_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 116 * (codeMat 403 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 273 ∈ actionW (codeMat 212) (codeMat 403) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 273 : Mat3).transpose = codeMat 273 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h1
    have hw : codeMat 104 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 104 (by decide)
    have hact : actionA (codeMat 212) (codeMat 403) (codeMat 104) = codeMat 33 := by
      unfold actionA; rw [step113_415s29_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 104 * (codeMat 403 : Mat3).transpose = codeMat 33
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 33 ∈ actionW (codeMat 212) (codeMat 403) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 33 : Mat3).transpose = codeMat 129 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h2
    have hw : codeMat 224 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 224 (by decide)
    have hact : actionA (codeMat 212) (codeMat 403) (codeMat 224) = codeMat 22 := by
      unfold actionA; rw [step113_415s29_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 224 * (codeMat 403 : Mat3).transpose = codeMat 22
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 22 ∈ actionW (codeMat 212) (codeMat 403) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 22 : Mat3).transpose = codeMat 88 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h3
    have hw : codeMat 119 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 119 (by decide)
    have hact : actionA (codeMat 212) (codeMat 403) (codeMat 119) = codeMat 145 := by
      unfold actionA; rw [step113_415s29_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 119 * (codeMat 403 : Mat3).transpose = codeMat 145
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 145 ∈ actionW (codeMat 212) (codeMat 403) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 145 : Mat3).transpose = codeMat 49 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h4
    have hw : codeMat 1 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 1 (by decide)
    have hact : actionA (codeMat 212) (codeMat 403) (codeMat 1) = codeMat 64 := by
      unfold actionA; rw [step113_415s29_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 1 * (codeMat 403 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 64 ∈ actionW (codeMat 212) (codeMat 403) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 64 : Mat3).transpose = codeMat 4 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h5
    have hw : codeMat 8 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 8 (by decide)
    have hact : actionA (codeMat 212) (codeMat 403) (codeMat 8) = codeMat 8 := by
      unfold actionA; rw [step113_415s29_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 8 * (codeMat 403 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 8 ∈ actionW (codeMat 212) (codeMat 403) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 8 : Mat3).transpose = codeMat 2 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans

theorem step113_415_row29_qr : QuotientRankAtLeast step113_415ActualSource29 15 := by
  have hP : Invertible (codeMat 212 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 403 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 212) (codeMat 403) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 212) (codeMat 403) hP hQ orbit35W 15 QiushiMatmul.orbit35_lb15
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 212) (codeMat 403) orbit35W)) 15 :=
    quotientRankAtLeast_transpose hAct
  exact quotientRankAtLeast_mono step113_415s29_source_le hT

-- Source 30: row 787, orbit 35, lb 15, cap 1
def step113_415ActualSource30 : Submodule F2 Mat3 := spanCodes [273, 144, 88, 33, 4, 2]

theorem step113_415_row30_W_le_source : o415W ≤ step113_415ActualSource30 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource30
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 144, 88, 33, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 144, 88, 33, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 144, 88, 33, 4, 2] 2 (by decide)

private theorem step113_415s30_QtInv :
    (codeMat 417 : Mat3).transpose⁻¹ = (codeMat 177 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 417 : Mat3).transpose * (codeMat 177 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s30_source_le :
    step113_415ActualSource30 ≤ transposeW (actionW (codeMat 354) (codeMat 417) orbit35W) := by
  apply step113_415_spanCodes_le_of_gens [273, 144, 88, 33, 4, 2]
    (transposeW (actionW (codeMat 354) (codeMat 417) orbit35W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 124 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 124 (by decide)
    have hact : actionA (codeMat 354) (codeMat 417) (codeMat 124) = codeMat 273 := by
      unfold actionA; rw [step113_415s30_QtInv]
      show (codeMat 354 : Mat3).transpose * codeMat 124 * (codeMat 177 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 273 ∈ actionW (codeMat 354) (codeMat 417) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 273 : Mat3).transpose = codeMat 273 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h1
    have hw : codeMat 2 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 2 (by decide)
    have hact : actionA (codeMat 354) (codeMat 417) (codeMat 2) = codeMat 48 := by
      unfold actionA; rw [step113_415s30_QtInv]
      show (codeMat 354 : Mat3).transpose * codeMat 2 * (codeMat 177 : Mat3).transpose = codeMat 48
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 48 ∈ actionW (codeMat 354) (codeMat 417) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 48 : Mat3).transpose = codeMat 144 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h2
    have hw : codeMat 148 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 148 (by decide)
    have hact : actionA (codeMat 354) (codeMat 417) (codeMat 148) = codeMat 22 := by
      unfold actionA; rw [step113_415s30_QtInv]
      show (codeMat 354 : Mat3).transpose * codeMat 148 * (codeMat 177 : Mat3).transpose = codeMat 22
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 22 ∈ actionW (codeMat 354) (codeMat 417) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 22 : Mat3).transpose = codeMat 88 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h3
    have hw : codeMat 104 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 104 (by decide)
    have hact : actionA (codeMat 354) (codeMat 417) (codeMat 104) = codeMat 129 := by
      unfold actionA; rw [step113_415s30_QtInv]
      show (codeMat 354 : Mat3).transpose * codeMat 104 * (codeMat 177 : Mat3).transpose = codeMat 129
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 129 ∈ actionW (codeMat 354) (codeMat 417) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 129 : Mat3).transpose = codeMat 33 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h4
    have hw : codeMat 8 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 8 (by decide)
    have hact : actionA (codeMat 354) (codeMat 417) (codeMat 8) = codeMat 64 := by
      unfold actionA; rw [step113_415s30_QtInv]
      show (codeMat 354 : Mat3).transpose * codeMat 8 * (codeMat 177 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 64 ∈ actionW (codeMat 354) (codeMat 417) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 64 : Mat3).transpose = codeMat 4 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h5
    have hw : codeMat 1 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 1 (by decide)
    have hact : actionA (codeMat 354) (codeMat 417) (codeMat 1) = codeMat 8 := by
      unfold actionA; rw [step113_415s30_QtInv]
      show (codeMat 354 : Mat3).transpose * codeMat 1 * (codeMat 177 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 8 ∈ actionW (codeMat 354) (codeMat 417) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 8 : Mat3).transpose = codeMat 2 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans

theorem step113_415_row30_qr : QuotientRankAtLeast step113_415ActualSource30 15 := by
  have hP : Invertible (codeMat 354 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 354) (codeMat 417) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 354) (codeMat 417) hP hQ orbit35W 15 QiushiMatmul.orbit35_lb15
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 354) (codeMat 417) orbit35W)) 15 :=
    quotientRankAtLeast_transpose hAct
  exact quotientRankAtLeast_mono step113_415s30_source_le hT

-- Source 31: row 788, orbit 35, lb 15, cap 1
def step113_415ActualSource31 : Submodule F2 Mat3 := spanCodes [273, 129, 89, 49, 4, 2]

theorem step113_415_row31_W_le_source : o415W ≤ step113_415ActualSource31 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource31
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 129, 89, 49, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 129, 89, 49, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 129, 89, 49, 4, 2] 2 (by decide)

private theorem step113_415s31_QtInv :
    (codeMat 401 : Mat3).transpose⁻¹ = (codeMat 401 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 401 : Mat3).transpose * (codeMat 401 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s31_source_le :
    step113_415ActualSource31 ≤ transposeW (actionW (codeMat 212) (codeMat 401) orbit35W) := by
  apply step113_415_spanCodes_le_of_gens [273, 129, 89, 49, 4, 2]
    (transposeW (actionW (codeMat 212) (codeMat 401) orbit35W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 124 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 124 (by decide)
    have hact : actionA (codeMat 212) (codeMat 401) (codeMat 124) = codeMat 273 := by
      unfold actionA; rw [step113_415s31_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 124 * (codeMat 401 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 273 ∈ actionW (codeMat 212) (codeMat 401) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 273 : Mat3).transpose = codeMat 273 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h1
    have hw : codeMat 104 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 104 (by decide)
    have hact : actionA (codeMat 212) (codeMat 401) (codeMat 104) = codeMat 33 := by
      unfold actionA; rw [step113_415s31_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 104 * (codeMat 401 : Mat3).transpose = codeMat 33
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 33 ∈ actionW (codeMat 212) (codeMat 401) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 33 : Mat3).transpose = codeMat 129 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h2
    have hw : codeMat 232 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 232 (by decide)
    have hact : actionA (codeMat 212) (codeMat 401) (codeMat 232) = codeMat 23 := by
      unfold actionA; rw [step113_415s31_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 232 * (codeMat 401 : Mat3).transpose = codeMat 23
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 23 ∈ actionW (codeMat 212) (codeMat 401) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 23 : Mat3).transpose = codeMat 89 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h3
    have hw : codeMat 126 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 126 (by decide)
    have hact : actionA (codeMat 212) (codeMat 401) (codeMat 126) = codeMat 145 := by
      unfold actionA; rw [step113_415s31_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 126 * (codeMat 401 : Mat3).transpose = codeMat 145
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 145 ∈ actionW (codeMat 212) (codeMat 401) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 145 : Mat3).transpose = codeMat 49 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h4
    have hw : codeMat 1 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 1 (by decide)
    have hact : actionA (codeMat 212) (codeMat 401) (codeMat 1) = codeMat 64 := by
      unfold actionA; rw [step113_415s31_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 1 * (codeMat 401 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 64 ∈ actionW (codeMat 212) (codeMat 401) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 64 : Mat3).transpose = codeMat 4 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h5
    have hw : codeMat 8 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 8 (by decide)
    have hact : actionA (codeMat 212) (codeMat 401) (codeMat 8) = codeMat 8 := by
      unfold actionA; rw [step113_415s31_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 8 * (codeMat 401 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 8 ∈ actionW (codeMat 212) (codeMat 401) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 8 : Mat3).transpose = codeMat 2 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans

theorem step113_415_row31_qr : QuotientRankAtLeast step113_415ActualSource31 15 := by
  have hP : Invertible (codeMat 212 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 212) (codeMat 401) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 212) (codeMat 401) hP hQ orbit35W 15 QiushiMatmul.orbit35_lb15
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 212) (codeMat 401) orbit35W)) 15 :=
    quotientRankAtLeast_transpose hAct
  exact quotientRankAtLeast_mono step113_415s31_source_le hT

-- Source 32: row 789, orbit 35, lb 15, cap 1
def step113_415ActualSource32 : Submodule F2 Mat3 := spanCodes [273, 145, 64, 33, 4, 2]

theorem step113_415_row32_W_le_source : o415W ≤ step113_415ActualSource32 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource32
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 145, 64, 33, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 145, 64, 33, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 145, 64, 33, 4, 2] 2 (by decide)

private theorem step113_415s32_QtInv :
    (codeMat 177 : Mat3).transpose⁻¹ = (codeMat 417 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 177 : Mat3).transpose * (codeMat 417 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s32_source_le :
    step113_415ActualSource32 ≤ transposeW (actionW (codeMat 86) (codeMat 177) orbit35W) := by
  apply step113_415_spanCodes_le_of_gens [273, 145, 64, 33, 4, 2]
    (transposeW (actionW (codeMat 86) (codeMat 177) orbit35W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 98 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 98 (by decide)
    have hact : actionA (codeMat 86) (codeMat 177) (codeMat 98) = codeMat 273 := by
      unfold actionA; rw [step113_415s32_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 98 * (codeMat 417 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 273 ∈ actionW (codeMat 86) (codeMat 177) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 273 : Mat3).transpose = codeMat 273 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h1
    have hw : codeMat 96 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 96 (by decide)
    have hact : actionA (codeMat 86) (codeMat 177) (codeMat 96) = codeMat 49 := by
      unfold actionA; rw [step113_415s32_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 96 * (codeMat 417 : Mat3).transpose = codeMat 49
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 49 ∈ actionW (codeMat 86) (codeMat 177) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 49 : Mat3).transpose = codeMat 145 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h2
    have hw : codeMat 128 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 128 (by decide)
    have hact : actionA (codeMat 86) (codeMat 177) (codeMat 128) = codeMat 4 := by
      unfold actionA; rw [step113_415s32_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 128 * (codeMat 417 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 4 ∈ actionW (codeMat 86) (codeMat 177) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 4 : Mat3).transpose = codeMat 64 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h3
    have hw : codeMat 118 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 118 (by decide)
    have hact : actionA (codeMat 86) (codeMat 177) (codeMat 118) = codeMat 129 := by
      unfold actionA; rw [step113_415s32_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 118 * (codeMat 417 : Mat3).transpose = codeMat 129
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 129 ∈ actionW (codeMat 86) (codeMat 177) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 129 : Mat3).transpose = codeMat 33 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h4
    have hw : codeMat 9 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 9 (by decide)
    have hact : actionA (codeMat 86) (codeMat 177) (codeMat 9) = codeMat 64 := by
      unfold actionA; rw [step113_415s32_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 9 * (codeMat 417 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 64 ∈ actionW (codeMat 86) (codeMat 177) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 64 : Mat3).transpose = codeMat 4 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h5
    have hw : codeMat 8 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 8 (by decide)
    have hact : actionA (codeMat 86) (codeMat 177) (codeMat 8) = codeMat 8 := by
      unfold actionA; rw [step113_415s32_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 8 * (codeMat 417 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 8 ∈ actionW (codeMat 86) (codeMat 177) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 8 : Mat3).transpose = codeMat 2 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans

theorem step113_415_row32_qr : QuotientRankAtLeast step113_415ActualSource32 15 := by
  have hP : Invertible (codeMat 86 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 86) (codeMat 177) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 86) (codeMat 177) hP hQ orbit35W 15 QiushiMatmul.orbit35_lb15
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 86) (codeMat 177) orbit35W)) 15 :=
    quotientRankAtLeast_transpose hAct
  exact quotientRankAtLeast_mono step113_415s32_source_le hT

-- Source 33: row 792, orbit 35, lb 15, cap 1
def step113_415ActualSource33 : Submodule F2 Mat3 := spanCodes [256, 160, 65, 17, 4, 2]

theorem step113_415_row33_W_le_source : o415W ≤ step113_415ActualSource33 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource33
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 65, 17, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 65, 17, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 65, 17, 4, 2] 2 (by decide)

private theorem step113_415s33_QtInv :
    (codeMat 165 : Mat3).transpose⁻¹ = (codeMat 163 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 165 : Mat3).transpose * (codeMat 163 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s33_source_le :
    step113_415ActualSource33 ≤ transposeW (actionW (codeMat 84) (codeMat 165) orbit35W) := by
  apply step113_415_spanCodes_le_of_gens [256, 160, 65, 17, 4, 2]
    (transposeW (actionW (codeMat 84) (codeMat 165) orbit35W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 3 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 3 (by decide)
    have hact : actionA (codeMat 84) (codeMat 165) (codeMat 3) = codeMat 256 := by
      unfold actionA; rw [step113_415s33_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 3 * (codeMat 163 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 256 ∈ actionW (codeMat 84) (codeMat 165) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 256 : Mat3).transpose = codeMat 256 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h1
    have hw : codeMat 28 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 28 (by decide)
    have hact : actionA (codeMat 84) (codeMat 165) (codeMat 28) = codeMat 160 := by
      unfold actionA; rw [step113_415s33_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 28 * (codeMat 163 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 160 ∈ actionW (codeMat 84) (codeMat 165) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 160 : Mat3).transpose = codeMat 160 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h2
    have hw : codeMat 128 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 165) (codeMat 128) = codeMat 5 := by
      unfold actionA; rw [step113_415s33_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 163 : Mat3).transpose = codeMat 5
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 5 ∈ actionW (codeMat 84) (codeMat 165) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 5 : Mat3).transpose = codeMat 65 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h3
    have hw : codeMat 96 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 96 (by decide)
    have hact : actionA (codeMat 84) (codeMat 165) (codeMat 96) = codeMat 17 := by
      unfold actionA; rw [step113_415s33_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 96 * (codeMat 163 : Mat3).transpose = codeMat 17
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 17 ∈ actionW (codeMat 84) (codeMat 165) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 17 : Mat3).transpose = codeMat 17 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h4
    have hw : codeMat 1 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 165) (codeMat 1) = codeMat 64 := by
      unfold actionA; rw [step113_415s33_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 163 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 64 ∈ actionW (codeMat 84) (codeMat 165) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 64 : Mat3).transpose = codeMat 4 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h5
    have hw : codeMat 8 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 165) (codeMat 8) = codeMat 8 := by
      unfold actionA; rw [step113_415s33_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 163 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 8 ∈ actionW (codeMat 84) (codeMat 165) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 8 : Mat3).transpose = codeMat 2 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans

theorem step113_415_row33_qr : QuotientRankAtLeast step113_415ActualSource33 15 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 165 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 165) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 165) hP hQ orbit35W 15 QiushiMatmul.orbit35_lb15
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 84) (codeMat 165) orbit35W)) 15 :=
    quotientRankAtLeast_transpose hAct
  exact quotientRankAtLeast_mono step113_415s33_source_le hT

-- Source 34: row 794, orbit 35, lb 15, cap 1
def step113_415ActualSource34 : Submodule F2 Mat3 := spanCodes [256, 129, 97, 17, 4, 2]

theorem step113_415_row34_W_le_source : o415W ≤ step113_415ActualSource34 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource34
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 129, 97, 17, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 129, 97, 17, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 129, 97, 17, 4, 2] 2 (by decide)

private theorem step113_415s34_QtInv :
    (codeMat 92 : Mat3).transpose⁻¹ = (codeMat 116 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 92 : Mat3).transpose * (codeMat 116 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s34_source_le :
    step113_415ActualSource34 ≤ actionW (codeMat 417) (codeMat 92) orbit35W := by
  apply step113_415_spanCodes_le_of_gens [256, 129, 97, 17, 4, 2]
    (actionW (codeMat 417) (codeMat 92) orbit35W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 8 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 8 (by decide)
    have hact : actionA (codeMat 417) (codeMat 92) (codeMat 8) = codeMat 256 := by
      unfold actionA; rw [step113_415s34_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 8 * (codeMat 116 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 22 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 22 (by decide)
    have hact : actionA (codeMat 417) (codeMat 92) (codeMat 22) = codeMat 129 := by
      unfold actionA; rw [step113_415s34_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 22 * (codeMat 116 : Mat3).transpose = codeMat 129
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 126 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 126 (by decide)
    have hact : actionA (codeMat 417) (codeMat 92) (codeMat 126) = codeMat 97 := by
      unfold actionA; rw [step113_415s34_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 126 * (codeMat 116 : Mat3).transpose = codeMat 97
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 150 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 150 (by decide)
    have hact : actionA (codeMat 417) (codeMat 92) (codeMat 150) = codeMat 17 := by
      unfold actionA; rw [step113_415s34_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 150 * (codeMat 116 : Mat3).transpose = codeMat 17
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 1 (by decide)
    have hact : actionA (codeMat 417) (codeMat 92) (codeMat 1) = codeMat 4 := by
      unfold actionA; rw [step113_415s34_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 1 * (codeMat 116 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 2 (by decide)
    have hact : actionA (codeMat 417) (codeMat 92) (codeMat 2) = codeMat 2 := by
      unfold actionA; rw [step113_415s34_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 2 * (codeMat 116 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row34_qr : QuotientRankAtLeast step113_415ActualSource34 15 := by
  have hP : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 92 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 417) (codeMat 92) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 417) (codeMat 92) hP hQ orbit35W 15 QiushiMatmul.orbit35_lb15
  exact quotientRankAtLeast_mono step113_415s34_source_le hAct

-- Source 35: row 795, orbit 35, lb 15, cap 1
def step113_415ActualSource35 : Submodule F2 Mat3 := spanCodes [256, 160, 64, 17, 4, 2]

theorem step113_415_row35_W_le_source : o415W ≤ step113_415ActualSource35 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource35
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 17, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 17, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 17, 4, 2] 2 (by decide)

private theorem step113_415s35_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s35_source_le :
    step113_415ActualSource35 ≤ transposeW (actionW (codeMat 84) (codeMat 161) orbit35W) := by
  apply step113_415_spanCodes_le_of_gens [256, 160, 64, 17, 4, 2]
    (transposeW (actionW (codeMat 84) (codeMat 161) orbit35W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 2 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 161) (codeMat 2) = codeMat 256 := by
      unfold actionA; rw [step113_415s35_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 161 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 256 ∈ actionW (codeMat 84) (codeMat 161) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 256 : Mat3).transpose = codeMat 256 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h1
    have hw : codeMat 20 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 20 (by decide)
    have hact : actionA (codeMat 84) (codeMat 161) (codeMat 20) = codeMat 160 := by
      unfold actionA; rw [step113_415s35_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 20 * (codeMat 161 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 160 ∈ actionW (codeMat 84) (codeMat 161) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 160 : Mat3).transpose = codeMat 160 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h2
    have hw : codeMat 128 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 161) (codeMat 128) = codeMat 4 := by
      unfold actionA; rw [step113_415s35_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 161 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 4 ∈ actionW (codeMat 84) (codeMat 161) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 4 : Mat3).transpose = codeMat 64 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h3
    have hw : codeMat 96 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 96 (by decide)
    have hact : actionA (codeMat 84) (codeMat 161) (codeMat 96) = codeMat 17 := by
      unfold actionA; rw [step113_415s35_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 96 * (codeMat 161 : Mat3).transpose = codeMat 17
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 17 ∈ actionW (codeMat 84) (codeMat 161) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 17 : Mat3).transpose = codeMat 17 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h4
    have hw : codeMat 1 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 161) (codeMat 1) = codeMat 64 := by
      unfold actionA; rw [step113_415s35_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 64 ∈ actionW (codeMat 84) (codeMat 161) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 64 : Mat3).transpose = codeMat 4 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h5
    have hw : codeMat 8 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 161) (codeMat 8) = codeMat 8 := by
      unfold actionA; rw [step113_415s35_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 161 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 8 ∈ actionW (codeMat 84) (codeMat 161) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 8 : Mat3).transpose = codeMat 2 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans

theorem step113_415_row35_qr : QuotientRankAtLeast step113_415ActualSource35 15 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 161) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 161) hP hQ orbit35W 15 QiushiMatmul.orbit35_lb15
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 84) (codeMat 161) orbit35W)) 15 :=
    quotientRankAtLeast_transpose hAct
  exact quotientRankAtLeast_mono step113_415s35_source_le hT

-- Source 36: row 796, orbit 35, lb 15, cap 1
def step113_415ActualSource36 : Submodule F2 Mat3 := spanCodes [257, 129, 96, 16, 4, 2]

theorem step113_415_row36_W_le_source : o415W ≤ step113_415ActualSource36 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource36
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [257, 129, 96, 16, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [257, 129, 96, 16, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [257, 129, 96, 16, 4, 2] 2 (by decide)

private theorem step113_415s36_QtInv :
    (codeMat 116 : Mat3).transpose⁻¹ = (codeMat 92 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 116 : Mat3).transpose * (codeMat 92 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s36_source_le :
    step113_415ActualSource36 ≤ actionW (codeMat 161) (codeMat 116) orbit35W := by
  apply step113_415_spanCodes_le_of_gens [257, 129, 96, 16, 4, 2]
    (actionW (codeMat 161) (codeMat 116) orbit35W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 28 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 28 (by decide)
    have hact : actionA (codeMat 161) (codeMat 116) (codeMat 28) = codeMat 257 := by
      unfold actionA; rw [step113_415s36_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 28 * (codeMat 92 : Mat3).transpose = codeMat 257
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 20 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 20 (by decide)
    have hact : actionA (codeMat 161) (codeMat 116) (codeMat 20) = codeMat 129 := by
      unfold actionA; rw [step113_415s36_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 20 * (codeMat 92 : Mat3).transpose = codeMat 129
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 224 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 224 (by decide)
    have hact : actionA (codeMat 161) (codeMat 116) (codeMat 224) = codeMat 96 := by
      unfold actionA; rw [step113_415s36_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 224 * (codeMat 92 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 128 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 128 (by decide)
    have hact : actionA (codeMat 161) (codeMat 116) (codeMat 128) = codeMat 16 := by
      unfold actionA; rw [step113_415s36_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 128 * (codeMat 92 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 3 (by decide)
    have hact : actionA (codeMat 161) (codeMat 116) (codeMat 3) = codeMat 4 := by
      unfold actionA; rw [step113_415s36_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 3 * (codeMat 92 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 116) (codeMat 2) = codeMat 2 := by
      unfold actionA; rw [step113_415s36_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 92 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row36_qr : QuotientRankAtLeast step113_415ActualSource36 15 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 116 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 116) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 116) hP hQ orbit35W 15 QiushiMatmul.orbit35_lb15
  exact quotientRankAtLeast_mono step113_415s36_source_le hAct

-- Source 37: row 799, orbit 35, lb 15, cap 1
def step113_415ActualSource37 : Submodule F2 Mat3 := spanCodes [273, 129, 72, 49, 4, 2]

theorem step113_415_row37_W_le_source : o415W ≤ step113_415ActualSource37 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource37
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 129, 72, 49, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 129, 72, 49, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 129, 72, 49, 4, 2] 2 (by decide)

private theorem step113_415s37_QtInv :
    (codeMat 401 : Mat3).transpose⁻¹ = (codeMat 401 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 401 : Mat3).transpose * (codeMat 401 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s37_source_le :
    step113_415ActualSource37 ≤ transposeW (actionW (codeMat 84) (codeMat 401) orbit35W) := by
  apply step113_415_spanCodes_le_of_gens [273, 129, 72, 49, 4, 2]
    (transposeW (actionW (codeMat 84) (codeMat 401) orbit35W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 116 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 116 (by decide)
    have hact : actionA (codeMat 84) (codeMat 401) (codeMat 116) = codeMat 273 := by
      unfold actionA; rw [step113_415s37_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 116 * (codeMat 401 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 273 ∈ actionW (codeMat 84) (codeMat 401) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 273 : Mat3).transpose = codeMat 273 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h1
    have hw : codeMat 96 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 96 (by decide)
    have hact : actionA (codeMat 84) (codeMat 401) (codeMat 96) = codeMat 33 := by
      unfold actionA; rw [step113_415s37_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 96 * (codeMat 401 : Mat3).transpose = codeMat 33
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 33 ∈ actionW (codeMat 84) (codeMat 401) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 33 : Mat3).transpose = codeMat 129 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h2
    have hw : codeMat 128 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 401) (codeMat 128) = codeMat 6 := by
      unfold actionA; rw [step113_415s37_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 401 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 6 ∈ actionW (codeMat 84) (codeMat 401) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 6 : Mat3).transpose = codeMat 72 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h3
    have hw : codeMat 118 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 118 (by decide)
    have hact : actionA (codeMat 84) (codeMat 401) (codeMat 118) = codeMat 145 := by
      unfold actionA; rw [step113_415s37_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 118 * (codeMat 401 : Mat3).transpose = codeMat 145
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 145 ∈ actionW (codeMat 84) (codeMat 401) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 145 : Mat3).transpose = codeMat 49 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h4
    have hw : codeMat 1 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 401) (codeMat 1) = codeMat 64 := by
      unfold actionA; rw [step113_415s37_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 401 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 64 ∈ actionW (codeMat 84) (codeMat 401) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 64 : Mat3).transpose = codeMat 4 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h5
    have hw : codeMat 8 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 401) (codeMat 8) = codeMat 8 := by
      unfold actionA; rw [step113_415s37_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 401 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 8 ∈ actionW (codeMat 84) (codeMat 401) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 8 : Mat3).transpose = codeMat 2 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans

theorem step113_415_row37_qr : QuotientRankAtLeast step113_415ActualSource37 15 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 401) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 401) hP hQ orbit35W 15 QiushiMatmul.orbit35_lb15
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 84) (codeMat 401) orbit35W)) 15 :=
    quotientRankAtLeast_transpose hAct
  exact quotientRankAtLeast_mono step113_415s37_source_le hT

-- Source 38: row 800, orbit 35, lb 15, cap 1
def step113_415ActualSource38 : Submodule F2 Mat3 := spanCodes [273, 144, 73, 33, 4, 2]

theorem step113_415_row38_W_le_source : o415W ≤ step113_415ActualSource38 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource38
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 144, 73, 33, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 144, 73, 33, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 144, 73, 33, 4, 2] 2 (by decide)

private theorem step113_415s38_QtInv :
    (codeMat 419 : Mat3).transpose⁻¹ = (codeMat 183 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 419 : Mat3).transpose * (codeMat 183 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s38_source_le :
    step113_415ActualSource38 ≤ transposeW (actionW (codeMat 98) (codeMat 419) orbit35W) := by
  apply step113_415_spanCodes_le_of_gens [273, 144, 73, 33, 4, 2]
    (transposeW (actionW (codeMat 98) (codeMat 419) orbit35W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 117 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 117 (by decide)
    have hact : actionA (codeMat 98) (codeMat 419) (codeMat 117) = codeMat 273 := by
      unfold actionA; rw [step113_415s38_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 117 * (codeMat 183 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 273 ∈ actionW (codeMat 98) (codeMat 419) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 273 : Mat3).transpose = codeMat 273 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h1
    have hw : codeMat 3 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 3 (by decide)
    have hact : actionA (codeMat 98) (codeMat 419) (codeMat 3) = codeMat 48 := by
      unfold actionA; rw [step113_415s38_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 3 * (codeMat 183 : Mat3).transpose = codeMat 48
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 48 ∈ actionW (codeMat 98) (codeMat 419) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 48 : Mat3).transpose = codeMat 144 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h2
    have hw : codeMat 128 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 128 (by decide)
    have hact : actionA (codeMat 98) (codeMat 419) (codeMat 128) = codeMat 7 := by
      unfold actionA; rw [step113_415s38_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 128 * (codeMat 183 : Mat3).transpose = codeMat 7
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 7 ∈ actionW (codeMat 98) (codeMat 419) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 7 : Mat3).transpose = codeMat 73 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h3
    have hw : codeMat 104 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 104 (by decide)
    have hact : actionA (codeMat 98) (codeMat 419) (codeMat 104) = codeMat 129 := by
      unfold actionA; rw [step113_415s38_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 104 * (codeMat 183 : Mat3).transpose = codeMat 129
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 129 ∈ actionW (codeMat 98) (codeMat 419) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 129 : Mat3).transpose = codeMat 33 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h4
    have hw : codeMat 8 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 8 (by decide)
    have hact : actionA (codeMat 98) (codeMat 419) (codeMat 8) = codeMat 64 := by
      unfold actionA; rw [step113_415s38_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 8 * (codeMat 183 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 64 ∈ actionW (codeMat 98) (codeMat 419) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 64 : Mat3).transpose = codeMat 4 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h5
    have hw : codeMat 1 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 1 (by decide)
    have hact : actionA (codeMat 98) (codeMat 419) (codeMat 1) = codeMat 8 := by
      unfold actionA; rw [step113_415s38_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 1 * (codeMat 183 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 8 ∈ actionW (codeMat 98) (codeMat 419) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 8 : Mat3).transpose = codeMat 2 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans

theorem step113_415_row38_qr : QuotientRankAtLeast step113_415ActualSource38 15 := by
  have hP : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 419 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 98) (codeMat 419) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 98) (codeMat 419) hP hQ orbit35W 15 QiushiMatmul.orbit35_lb15
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 98) (codeMat 419) orbit35W)) 15 :=
    quotientRankAtLeast_transpose hAct
  exact quotientRankAtLeast_mono step113_415s38_source_le hT

-- Source 39: row 801, orbit 35, lb 15, cap 1
def step113_415ActualSource39 : Submodule F2 Mat3 := spanCodes [273, 145, 89, 49, 4, 2]

theorem step113_415_row39_W_le_source : o415W ≤ step113_415ActualSource39 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource39
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 145, 89, 49, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 145, 89, 49, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 145, 89, 49, 4, 2] 2 (by decide)

private theorem step113_415s39_QtInv :
    (codeMat 86 : Mat3).transpose⁻¹ = (codeMat 212 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 86 : Mat3).transpose * (codeMat 212 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s39_source_le :
    step113_415ActualSource39 ≤ actionW (codeMat 305) (codeMat 86) orbit35W := by
  apply step113_415_spanCodes_le_of_gens [273, 145, 89, 49, 4, 2]
    (actionW (codeMat 305) (codeMat 86) orbit35W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 156 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 156 (by decide)
    have hact : actionA (codeMat 305) (codeMat 86) (codeMat 156) = codeMat 273 := by
      unfold actionA; rw [step113_415s39_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 156 * (codeMat 212 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 28 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 28 (by decide)
    have hact : actionA (codeMat 305) (codeMat 86) (codeMat 28) = codeMat 145 := by
      unfold actionA; rw [step113_415s39_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 28 * (codeMat 212 : Mat3).transpose = codeMat 145
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 252 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 252 (by decide)
    have hact : actionA (codeMat 305) (codeMat 86) (codeMat 252) = codeMat 89 := by
      unfold actionA; rw [step113_415s39_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 252 * (codeMat 212 : Mat3).transpose = codeMat 89
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 148 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 148 (by decide)
    have hact : actionA (codeMat 305) (codeMat 86) (codeMat 148) = codeMat 49 := by
      unfold actionA; rw [step113_415s39_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 148 * (codeMat 212 : Mat3).transpose = codeMat 49
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 1 (by decide)
    have hact : actionA (codeMat 305) (codeMat 86) (codeMat 1) = codeMat 4 := by
      unfold actionA; rw [step113_415s39_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 1 * (codeMat 212 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 3 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 3 (by decide)
    have hact : actionA (codeMat 305) (codeMat 86) (codeMat 3) = codeMat 2 := by
      unfold actionA; rw [step113_415s39_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 3 * (codeMat 212 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row39_qr : QuotientRankAtLeast step113_415ActualSource39 15 := by
  have hP : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 86 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 305) (codeMat 86) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 305) (codeMat 86) hP hQ orbit35W 15 QiushiMatmul.orbit35_lb15
  exact quotientRankAtLeast_mono step113_415s39_source_le hAct

-- Source 40: row 803, orbit 35, lb 15, cap 1
def step113_415ActualSource40 : Submodule F2 Mat3 := spanCodes [273, 144, 89, 48, 4, 2]

theorem step113_415_row40_W_le_source : o415W ≤ step113_415ActualSource40 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource40
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 144, 89, 48, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 144, 89, 48, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 144, 89, 48, 4, 2] 2 (by decide)

private theorem step113_415s40_QtInv :
    (codeMat 110 : Mat3).transpose⁻¹ = (codeMat 444 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 110 : Mat3).transpose * (codeMat 444 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s40_source_le :
    step113_415ActualSource40 ≤ actionW (codeMat 177) (codeMat 110) orbit35W := by
  apply step113_415_spanCodes_le_of_gens [273, 144, 89, 48, 4, 2]
    (actionW (codeMat 177) (codeMat 110) orbit35W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 158 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 158 (by decide)
    have hact : actionA (codeMat 177) (codeMat 110) (codeMat 158) = codeMat 273 := by
      unfold actionA; rw [step113_415s40_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 158 * (codeMat 444 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 8 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 8 (by decide)
    have hact : actionA (codeMat 177) (codeMat 110) (codeMat 8) = codeMat 144 := by
      unfold actionA; rw [step113_415s40_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 8 * (codeMat 444 : Mat3).transpose = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 118 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 118 (by decide)
    have hact : actionA (codeMat 177) (codeMat 110) (codeMat 118) = codeMat 89 := by
      unfold actionA; rw [step113_415s40_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 118 * (codeMat 444 : Mat3).transpose = codeMat 89
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 128 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 128 (by decide)
    have hact : actionA (codeMat 177) (codeMat 110) (codeMat 128) = codeMat 48 := by
      unfold actionA; rw [step113_415s40_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 128 * (codeMat 444 : Mat3).transpose = codeMat 48
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 3 (by decide)
    have hact : actionA (codeMat 177) (codeMat 110) (codeMat 3) = codeMat 4 := by
      unfold actionA; rw [step113_415s40_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 3 * (codeMat 444 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 110) (codeMat 1) = codeMat 2 := by
      unfold actionA; rw [step113_415s40_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * (codeMat 444 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row40_qr : QuotientRankAtLeast step113_415ActualSource40 15 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 110 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 110) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 110) hP hQ orbit35W 15 QiushiMatmul.orbit35_lb15
  exact quotientRankAtLeast_mono step113_415s40_source_le hAct

-- Source 41: row 804, orbit 35, lb 15, cap 1
def step113_415ActualSource41 : Submodule F2 Mat3 := spanCodes [273, 144, 72, 33, 4, 2]

theorem step113_415_row41_W_le_source : o415W ≤ step113_415ActualSource41 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource41
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 144, 72, 33, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 144, 72, 33, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 144, 72, 33, 4, 2] 2 (by decide)

private theorem step113_415s41_QtInv :
    (codeMat 417 : Mat3).transpose⁻¹ = (codeMat 177 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 417 : Mat3).transpose * (codeMat 177 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s41_source_le :
    step113_415ActualSource41 ≤ transposeW (actionW (codeMat 98) (codeMat 417) orbit35W) := by
  apply step113_415_spanCodes_le_of_gens [273, 144, 72, 33, 4, 2]
    (transposeW (actionW (codeMat 98) (codeMat 417) orbit35W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 116 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 116 (by decide)
    have hact : actionA (codeMat 98) (codeMat 417) (codeMat 116) = codeMat 273 := by
      unfold actionA; rw [step113_415s41_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 116 * (codeMat 177 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 273 ∈ actionW (codeMat 98) (codeMat 417) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 273 : Mat3).transpose = codeMat 273 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h1
    have hw : codeMat 2 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 2 (by decide)
    have hact : actionA (codeMat 98) (codeMat 417) (codeMat 2) = codeMat 48 := by
      unfold actionA; rw [step113_415s41_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 2 * (codeMat 177 : Mat3).transpose = codeMat 48
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 48 ∈ actionW (codeMat 98) (codeMat 417) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 48 : Mat3).transpose = codeMat 144 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h2
    have hw : codeMat 128 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 128 (by decide)
    have hact : actionA (codeMat 98) (codeMat 417) (codeMat 128) = codeMat 6 := by
      unfold actionA; rw [step113_415s41_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 128 * (codeMat 177 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 6 ∈ actionW (codeMat 98) (codeMat 417) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 6 : Mat3).transpose = codeMat 72 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h3
    have hw : codeMat 96 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 96 (by decide)
    have hact : actionA (codeMat 98) (codeMat 417) (codeMat 96) = codeMat 129 := by
      unfold actionA; rw [step113_415s41_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 96 * (codeMat 177 : Mat3).transpose = codeMat 129
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 129 ∈ actionW (codeMat 98) (codeMat 417) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 129 : Mat3).transpose = codeMat 33 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h4
    have hw : codeMat 8 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 8 (by decide)
    have hact : actionA (codeMat 98) (codeMat 417) (codeMat 8) = codeMat 64 := by
      unfold actionA; rw [step113_415s41_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 8 * (codeMat 177 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 64 ∈ actionW (codeMat 98) (codeMat 417) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 64 : Mat3).transpose = codeMat 4 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h5
    have hw : codeMat 1 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 1 (by decide)
    have hact : actionA (codeMat 98) (codeMat 417) (codeMat 1) = codeMat 8 := by
      unfold actionA; rw [step113_415s41_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 1 * (codeMat 177 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 8 ∈ actionW (codeMat 98) (codeMat 417) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 8 : Mat3).transpose = codeMat 2 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans

theorem step113_415_row41_qr : QuotientRankAtLeast step113_415ActualSource41 15 := by
  have hP : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 98) (codeMat 417) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 98) (codeMat 417) hP hQ orbit35W 15 QiushiMatmul.orbit35_lb15
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 98) (codeMat 417) orbit35W)) 15 :=
    quotientRankAtLeast_transpose hAct
  exact quotientRankAtLeast_mono step113_415s41_source_le hT

-- Source 42: row 2187, orbit 10, lb 12, cap 4
def step113_415ActualSource42 : Submodule F2 Mat3 := spanCodes [257, 137, 64, 32, 16, 4, 2]

theorem step113_415_row42_W_le_source : o415W ≤ step113_415ActualSource42 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource42
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [257, 137, 64, 32, 16, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [257, 137, 64, 32, 16, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [257, 137, 64, 32, 16, 4, 2] 2 (by decide)

private theorem step113_415s42_QtInv :
    (codeMat 114 : Mat3).transpose⁻¹ = (codeMat 204 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 114 : Mat3).transpose * (codeMat 204 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s42_source_le :
    step113_415ActualSource42 ≤ actionW (codeMat 266) (codeMat 114) orbit10W := by
  apply step113_415_spanCodes_le_of_gens [257, 137, 64, 32, 16, 4, 2]
    (actionW (codeMat 266) (codeMat 114) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 266) (codeMat 114) (codeMat 160) = codeMat 257 := by
      unfold actionA; rw [step113_415s42_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 160 * (codeMat 204 : Mat3).transpose = codeMat 257
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 228 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 228 (by decide)
    have hact : actionA (codeMat 266) (codeMat 114) (codeMat 228) = codeMat 137 := by
      unfold actionA; rw [step113_415s42_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 228 * (codeMat 204 : Mat3).transpose = codeMat 137
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 266) (codeMat 114) (codeMat 256) = codeMat 64 := by
      unfold actionA; rw [step113_415s42_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 256 * (codeMat 204 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 114) (codeMat 2) = codeMat 32 := by
      unfold actionA; rw [step113_415s42_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 204 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 3 (by decide)
    have hact : actionA (codeMat 266) (codeMat 114) (codeMat 3) = codeMat 16 := by
      unfold actionA; rw [step113_415s42_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 3 * (codeMat 204 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 114) (codeMat 16) = codeMat 4 := by
      unfold actionA; rw [step113_415s42_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 204 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 24 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide)
    have hact : actionA (codeMat 266) (codeMat 114) (codeMat 24) = codeMat 2 := by
      unfold actionA; rw [step113_415s42_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 24 * (codeMat 204 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row42_qr : QuotientRankAtLeast step113_415ActualSource42 12 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 114 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 114) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 114) hP hQ orbit10W 12 QiushiMatmul.orbit10_lb12
  exact quotientRankAtLeast_mono step113_415s42_source_le hAct

-- Source 43: row 2566, orbit 2, lb 6, cap 10
def step113_415ActualSource43 : Submodule F2 Mat3 := spanCodes [272, 128, 64, 32, 8, 4, 2, 1]

theorem step113_415_row43_W_le_source : o415W ≤ step113_415ActualSource43 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource43
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 128, 64, 32, 8, 4, 2, 1] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 128, 64, 32, 8, 4, 2, 1] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 128, 64, 32, 8, 4, 2, 1] 2 (by decide)

private theorem step113_415s43_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s43_source_le :
    step113_415ActualSource43 ≤ actionW (codeMat 161) (codeMat 273) flatW_2 := by
  apply step113_415_spanCodes_le_of_gens [272, 128, 64, 32, 8, 4, 2, 1]
    (actionW (codeMat 161) (codeMat 273) flatW_2)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 160 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 160) = codeMat 272 := by
      unfold actionA; rw [step113_415s43_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * (codeMat 273 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 16 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 16 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 16) = codeMat 128 := by
      unfold actionA; rw [step113_415s43_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 16 * (codeMat 273 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 8) = codeMat 64 := by
      unfold actionA; rw [step113_415s43_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 8 * (codeMat 273 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 256) = codeMat 32 := by
      unfold actionA; rw [step113_415s43_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 256 * (codeMat 273 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 64 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 64 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 64) = codeMat 8 := by
      unfold actionA; rw [step113_415s43_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 64 * (codeMat 273 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 4 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 4 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 4) = codeMat 4 := by
      unfold actionA; rw [step113_415s43_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 4 * (codeMat 273 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 2) = codeMat 2 := by
      unfold actionA; rw [step113_415s43_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 1 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA; rw [step113_415s43_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row43_qr : QuotientRankAtLeast step113_415ActualSource43 6 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 273) flatW_2) 6 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 273) hP hQ flatW_2 6 QiushiMatmul.flatSeed_2
  exact quotientRankAtLeast_mono step113_415s43_source_le hAct

-- Source 44: row 2573, orbit 2, lb 6, cap 10
def step113_415ActualSource44 : Submodule F2 Mat3 := spanCodes [264, 128, 72, 32, 24, 4, 2, 1]

theorem step113_415_row44_W_le_source : o415W ≤ step113_415ActualSource44 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource44
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [264, 128, 72, 32, 24, 4, 2, 1] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [264, 128, 72, 32, 24, 4, 2, 1] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [264, 128, 72, 32, 24, 4, 2, 1] 2 (by decide)

private theorem step113_415s44_QtInv :
    (codeMat 345 : Mat3).transpose⁻¹ = (codeMat 345 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 345 : Mat3).transpose * (codeMat 345 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s44_source_le :
    step113_415ActualSource44 ≤ actionW (codeMat 161) (codeMat 345) flatW_2 := by
  apply step113_415_spanCodes_le_of_gens [264, 128, 72, 32, 24, 4, 2, 1]
    (actionW (codeMat 161) (codeMat 345) flatW_2)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 480 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 480 (by decide)
    have hact : actionA (codeMat 161) (codeMat 345) (codeMat 480) = codeMat 264 := by
      unfold actionA; rw [step113_415s44_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 480 * (codeMat 345 : Mat3).transpose = codeMat 264
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 16 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 16 (by decide)
    have hact : actionA (codeMat 161) (codeMat 345) (codeMat 16) = codeMat 128 := by
      unfold actionA; rw [step113_415s44_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 16 * (codeMat 345 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 504 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 504 (by decide)
    have hact : actionA (codeMat 161) (codeMat 345) (codeMat 504) = codeMat 72 := by
      unfold actionA; rw [step113_415s44_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 504 * (codeMat 345 : Mat3).transpose = codeMat 72
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 161) (codeMat 345) (codeMat 256) = codeMat 32 := by
      unfold actionA; rw [step113_415s44_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 256 * (codeMat 345 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 320 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 320 (by decide)
    have hact : actionA (codeMat 161) (codeMat 345) (codeMat 320) = codeMat 24 := by
      unfold actionA; rw [step113_415s44_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 320 * (codeMat 345 : Mat3).transpose = codeMat 24
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 4 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 4 (by decide)
    have hact : actionA (codeMat 161) (codeMat 345) (codeMat 4) = codeMat 4 := by
      unfold actionA; rw [step113_415s44_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 4 * (codeMat 345 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 345) (codeMat 2) = codeMat 2 := by
      unfold actionA; rw [step113_415s44_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 345 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 7 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 7 (by decide)
    have hact : actionA (codeMat 161) (codeMat 345) (codeMat 7) = codeMat 1 := by
      unfold actionA; rw [step113_415s44_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 7 * (codeMat 345 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row44_qr : QuotientRankAtLeast step113_415ActualSource44 6 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 345 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 345) flatW_2) 6 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 345) hP hQ flatW_2 6 QiushiMatmul.flatSeed_2
  exact quotientRankAtLeast_mono step113_415s44_source_le hAct

-- Source 45: row 2602, orbit 2, lb 6, cap 10
def step113_415ActualSource45 : Submodule F2 Mat3 := spanCodes [264, 128, 64, 32, 24, 4, 2, 1]

theorem step113_415_row45_W_le_source : o415W ≤ step113_415ActualSource45 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource45
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [264, 128, 64, 32, 24, 4, 2, 1] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [264, 128, 64, 32, 24, 4, 2, 1] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [264, 128, 64, 32, 24, 4, 2, 1] 2 (by decide)

private theorem step113_415s45_QtInv :
    (codeMat 281 : Mat3).transpose⁻¹ = (codeMat 281 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 281 : Mat3).transpose * (codeMat 281 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s45_source_le :
    step113_415ActualSource45 ≤ actionW (codeMat 161) (codeMat 281) flatW_2 := by
  apply step113_415_spanCodes_le_of_gens [264, 128, 64, 32, 24, 4, 2, 1]
    (actionW (codeMat 161) (codeMat 281) flatW_2)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 224 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 224 (by decide)
    have hact : actionA (codeMat 161) (codeMat 281) (codeMat 224) = codeMat 264 := by
      unfold actionA; rw [step113_415s45_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 224 * (codeMat 281 : Mat3).transpose = codeMat 264
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 16 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 16 (by decide)
    have hact : actionA (codeMat 161) (codeMat 281) (codeMat 16) = codeMat 128 := by
      unfold actionA; rw [step113_415s45_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 16 * (codeMat 281 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 24 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 24 (by decide)
    have hact : actionA (codeMat 161) (codeMat 281) (codeMat 24) = codeMat 64 := by
      unfold actionA; rw [step113_415s45_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 24 * (codeMat 281 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 161) (codeMat 281) (codeMat 256) = codeMat 32 := by
      unfold actionA; rw [step113_415s45_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 256 * (codeMat 281 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 64 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 64 (by decide)
    have hact : actionA (codeMat 161) (codeMat 281) (codeMat 64) = codeMat 24 := by
      unfold actionA; rw [step113_415s45_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 64 * (codeMat 281 : Mat3).transpose = codeMat 24
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 4 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 4 (by decide)
    have hact : actionA (codeMat 161) (codeMat 281) (codeMat 4) = codeMat 4 := by
      unfold actionA; rw [step113_415s45_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 4 * (codeMat 281 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 281) (codeMat 2) = codeMat 2 := by
      unfold actionA; rw [step113_415s45_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 281 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 3 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 161) (codeMat 281) (codeMat 3) = codeMat 1 := by
      unfold actionA; rw [step113_415s45_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 3 * (codeMat 281 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row45_qr : QuotientRankAtLeast step113_415ActualSource45 6 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 281 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 281) flatW_2) 6 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 281) hP hQ flatW_2 6 QiushiMatmul.flatSeed_2
  exact quotientRankAtLeast_mono step113_415s45_source_le hAct

-- Source 46: row 44, orbit 101, lb 15, cap 1
def step113_415ActualSource46 : Submodule F2 Mat3 := spanCodes [273, 128, 81, 4, 2]

theorem step113_415_row46_W_le_source : o415W ≤ step113_415ActualSource46 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource46
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 128, 81, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 128, 81, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 128, 81, 4, 2] 2 (by decide)

private theorem step113_415s46_QtInv :
    (codeMat 330 : Mat3).transpose⁻¹ = (codeMat 394 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 330 : Mat3).transpose * (codeMat 394 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s46_source_le :
    step113_415ActualSource46 ≤ actionW (codeMat 140) (codeMat 330) orbit101W := by
  apply step113_415_spanCodes_le_of_gens [273, 128, 81, 4, 2]
    (actionW (codeMat 140) (codeMat 330) orbit101W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 116 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 116 (by decide)
    have hact : actionA (codeMat 140) (codeMat 330) (codeMat 116) = codeMat 273 := by
      unfold actionA; rw [step113_415s46_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 116 * (codeMat 394 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 1 (by decide)
    have hact : actionA (codeMat 140) (codeMat 330) (codeMat 1) = codeMat 128 := by
      unfold actionA; rw [step113_415s46_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 1 * (codeMat 394 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 118 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 118 (by decide)
    have hact : actionA (codeMat 140) (codeMat 330) (codeMat 118) = codeMat 81 := by
      unfold actionA; rw [step113_415s46_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 118 * (codeMat 394 : Mat3).transpose = codeMat 81
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 32 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 32 (by decide)
    have hact : actionA (codeMat 140) (codeMat 330) (codeMat 32) = codeMat 4 := by
      unfold actionA; rw [step113_415s46_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 32 * (codeMat 394 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 8 (by decide)
    have hact : actionA (codeMat 140) (codeMat 330) (codeMat 8) = codeMat 2 := by
      unfold actionA; rw [step113_415s46_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 8 * (codeMat 394 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row46_qr : QuotientRankAtLeast step113_415ActualSource46 15 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 330 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 330) orbit101W) 15 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 330) hP hQ orbit101W 15 QiushiMatmul.orbit101_lb15
  exact quotientRankAtLeast_mono step113_415s46_source_le hAct

-- Source 47: row 46, orbit 101, lb 15, cap 1
def step113_415ActualSource47 : Submodule F2 Mat3 := spanCodes [273, 161, 120, 4, 2]

theorem step113_415_row47_W_le_source : o415W ≤ step113_415ActualSource47 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource47
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 161, 120, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 161, 120, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 161, 120, 4, 2] 2 (by decide)

private theorem step113_415s47_QtInv :
    (codeMat 458 : Mat3).transpose⁻¹ = (codeMat 458 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 458 : Mat3).transpose * (codeMat 458 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s47_source_le :
    step113_415ActualSource47 ≤ actionW (codeMat 143) (codeMat 458) orbit101W := by
  apply step113_415_spanCodes_le_of_gens [273, 161, 120, 4, 2]
    (actionW (codeMat 143) (codeMat 458) orbit101W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 84 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 84 (by decide)
    have hact : actionA (codeMat 143) (codeMat 458) (codeMat 84) = codeMat 273 := by
      unfold actionA; rw [step113_415s47_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 84 * (codeMat 458 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 93 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 93 (by decide)
    have hact : actionA (codeMat 143) (codeMat 458) (codeMat 93) = codeMat 161 := by
      unfold actionA; rw [step113_415s47_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 93 * (codeMat 458 : Mat3).transpose = codeMat 161
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 118 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 118 (by decide)
    have hact : actionA (codeMat 143) (codeMat 458) (codeMat 118) = codeMat 120 := by
      unfold actionA; rw [step113_415s47_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 118 * (codeMat 458 : Mat3).transpose = codeMat 120
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 32 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 32 (by decide)
    have hact : actionA (codeMat 143) (codeMat 458) (codeMat 32) = codeMat 4 := by
      unfold actionA; rw [step113_415s47_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 32 * (codeMat 458 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 40 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 40 (by decide)
    have hact : actionA (codeMat 143) (codeMat 458) (codeMat 40) = codeMat 2 := by
      unfold actionA; rw [step113_415s47_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 40 * (codeMat 458 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row47_qr : QuotientRankAtLeast step113_415ActualSource47 15 := by
  have hP : Invertible (codeMat 143 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 458 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 143) (codeMat 458) orbit101W) 15 :=
    @quotientRankAtLeast_action (codeMat 143) (codeMat 458) hP hQ orbit101W 15 QiushiMatmul.orbit101_lb15
  exact quotientRankAtLeast_mono step113_415s47_source_le hAct

-- Source 48: row 48, orbit 101, lb 15, cap 1
def step113_415ActualSource48 : Submodule F2 Mat3 := spanCodes [273, 161, 72, 4, 2]

theorem step113_415_row48_W_le_source : o415W ≤ step113_415ActualSource48 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource48
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 161, 72, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 161, 72, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 161, 72, 4, 2] 2 (by decide)

private theorem step113_415s48_QtInv :
    (codeMat 394 : Mat3).transpose⁻¹ = (codeMat 330 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 394 : Mat3).transpose * (codeMat 330 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s48_source_le :
    step113_415ActualSource48 ≤ actionW (codeMat 142) (codeMat 394) orbit101W := by
  apply step113_415_spanCodes_le_of_gens [273, 161, 72, 4, 2]
    (actionW (codeMat 142) (codeMat 394) orbit101W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 84 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 84 (by decide)
    have hact : actionA (codeMat 142) (codeMat 394) (codeMat 84) = codeMat 273 := by
      unfold actionA; rw [step113_415s48_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 84 * (codeMat 330 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 85 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 85 (by decide)
    have hact : actionA (codeMat 142) (codeMat 394) (codeMat 85) = codeMat 161 := by
      unfold actionA; rw [step113_415s48_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 85 * (codeMat 330 : Mat3).transpose = codeMat 161
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 2 (by decide)
    have hact : actionA (codeMat 142) (codeMat 394) (codeMat 2) = codeMat 72 := by
      unfold actionA; rw [step113_415s48_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 2 * (codeMat 330 : Mat3).transpose = codeMat 72
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 32 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 32 (by decide)
    have hact : actionA (codeMat 142) (codeMat 394) (codeMat 32) = codeMat 4 := by
      unfold actionA; rw [step113_415s48_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 32 * (codeMat 330 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 40 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 40 (by decide)
    have hact : actionA (codeMat 142) (codeMat 394) (codeMat 40) = codeMat 2 := by
      unfold actionA; rw [step113_415s48_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 40 * (codeMat 330 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row48_qr : QuotientRankAtLeast step113_415ActualSource48 15 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 394 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 394) orbit101W) 15 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 394) hP hQ orbit101W 15 QiushiMatmul.orbit101_lb15
  exact quotientRankAtLeast_mono step113_415s48_source_le hAct

-- Source 49: row 55, orbit 103, lb 15, cap 1
def step113_415ActualSource49 : Submodule F2 Mat3 := spanCodes [257, 41, 16, 4, 2]

theorem step113_415_row49_W_le_source : o415W ≤ step113_415ActualSource49 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource49
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [257, 41, 16, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [257, 41, 16, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [257, 41, 16, 4, 2] 2 (by decide)

private theorem step113_415s49_QtInv :
    (codeMat 106 : Mat3).transpose⁻¹ = (codeMat 396 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 106 : Mat3).transpose * (codeMat 396 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s49_source_le :
    step113_415ActualSource49 ≤ actionW (codeMat 281) (codeMat 106) o103W_mono := by
  apply step113_415_spanCodes_le_of_gens [257, 41, 16, 4, 2]
    (actionW (codeMat 281) (codeMat 106) o103W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 134 ∈ o103W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 8, 2, 1] 134 (by decide)
    have hact : actionA (codeMat 281) (codeMat 106) (codeMat 134) = codeMat 257 := by
      unfold actionA; rw [step113_415s49_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 134 * (codeMat 396 : Mat3).transpose = codeMat 257
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 34 ∈ o103W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 8, 2, 1] 34 (by decide)
    have hact : actionA (codeMat 281) (codeMat 106) (codeMat 34) = codeMat 41 := by
      unfold actionA; rw [step113_415s49_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 34 * (codeMat 396 : Mat3).transpose = codeMat 41
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 9 ∈ o103W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 8, 2, 1] 9 (by decide)
    have hact : actionA (codeMat 281) (codeMat 106) (codeMat 9) = codeMat 16 := by
      unfold actionA; rw [step113_415s49_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 9 * (codeMat 396 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ o103W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 281) (codeMat 106) (codeMat 2) = codeMat 4 := by
      unfold actionA; rw [step113_415s49_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 2 * (codeMat 396 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o103W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 281) (codeMat 106) (codeMat 1) = codeMat 2 := by
      unfold actionA; rw [step113_415s49_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 1 * (codeMat 396 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row49_qr : QuotientRankAtLeast step113_415ActualSource49 15 := by
  have hP : Invertible (codeMat 281 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 106 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 281) (codeMat 106) o103W_mono) 15 :=
    @quotientRankAtLeast_action (codeMat 281) (codeMat 106) hP hQ o103W_mono 15 QiushiMatmul.orbit103_lb15_mono
  exact quotientRankAtLeast_mono step113_415s49_source_le hAct

-- Source 50: row 57, orbit 103, lb 15, cap 1
def step113_415ActualSource50 : Submodule F2 Mat3 := spanCodes [256, 65, 17, 4, 2]

theorem step113_415_row50_W_le_source : o415W ≤ step113_415ActualSource50 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource50
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 65, 17, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 65, 17, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 65, 17, 4, 2] 2 (by decide)

private theorem step113_415s50_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s50_source_le :
    step113_415ActualSource50 ≤ actionW (codeMat 169) (codeMat 84) o103W_mono := by
  apply step113_415_spanCodes_le_of_gens [256, 65, 17, 4, 2]
    (actionW (codeMat 169) (codeMat 84) o103W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 9 ∈ o103W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 8, 2, 1] 9 (by decide)
    have hact : actionA (codeMat 169) (codeMat 84) (codeMat 9) = codeMat 256 := by
      unfold actionA; rw [step113_415s50_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 9 * (codeMat 84 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 32 ∈ o103W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 169) (codeMat 84) (codeMat 32) = codeMat 65 := by
      unfold actionA; rw [step113_415s50_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 32 * (codeMat 84 : Mat3).transpose = codeMat 65
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 132 ∈ o103W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 8, 2, 1] 132 (by decide)
    have hact : actionA (codeMat 169) (codeMat 84) (codeMat 132) = codeMat 17 := by
      unfold actionA; rw [step113_415s50_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 132 * (codeMat 84 : Mat3).transpose = codeMat 17
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o103W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 84) (codeMat 1) = codeMat 4 := by
      unfold actionA; rw [step113_415s50_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * (codeMat 84 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o103W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 169) (codeMat 84) (codeMat 2) = codeMat 2 := by
      unfold actionA; rw [step113_415s50_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 2 * (codeMat 84 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row50_qr : QuotientRankAtLeast step113_415ActualSource50 15 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 84) o103W_mono) 15 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 84) hP hQ o103W_mono 15 QiushiMatmul.orbit103_lb15_mono
  exact quotientRankAtLeast_mono step113_415s50_source_le hAct

-- Source 51: row 69, orbit 103, lb 15, cap 1
def step113_415ActualSource51 : Submodule F2 Mat3 := spanCodes [273, 144, 120, 4, 2]

theorem step113_415_row51_W_le_source : o415W ≤ step113_415ActualSource51 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource51
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 144, 120, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 144, 120, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 144, 120, 4, 2] 2 (by decide)

private theorem step113_415s51_QtInv :
    (codeMat 110 : Mat3).transpose⁻¹ = (codeMat 444 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 110 : Mat3).transpose * (codeMat 444 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s51_source_le :
    step113_415ActualSource51 ≤ actionW (codeMat 313) (codeMat 110) o103W_mono := by
  apply step113_415_spanCodes_le_of_gens [273, 144, 120, 4, 2]
    (actionW (codeMat 313) (codeMat 110) o103W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 143 ∈ o103W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 8, 2, 1] 143 (by decide)
    have hact : actionA (codeMat 313) (codeMat 110) (codeMat 143) = codeMat 273 := by
      unfold actionA; rw [step113_415s51_QtInv]
      show (codeMat 313 : Mat3).transpose * codeMat 143 * (codeMat 444 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 9 ∈ o103W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 8, 2, 1] 9 (by decide)
    have hact : actionA (codeMat 313) (codeMat 110) (codeMat 9) = codeMat 144 := by
      unfold actionA; rw [step113_415s51_QtInv]
      show (codeMat 313 : Mat3).transpose * codeMat 9 * (codeMat 444 : Mat3).transpose = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 164 ∈ o103W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 8, 2, 1] 164 (by decide)
    have hact : actionA (codeMat 313) (codeMat 110) (codeMat 164) = codeMat 120 := by
      unfold actionA; rw [step113_415s51_QtInv]
      show (codeMat 313 : Mat3).transpose * codeMat 164 * (codeMat 444 : Mat3).transpose = codeMat 120
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 3 ∈ o103W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 8, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 313) (codeMat 110) (codeMat 3) = codeMat 4 := by
      unfold actionA; rw [step113_415s51_QtInv]
      show (codeMat 313 : Mat3).transpose * codeMat 3 * (codeMat 444 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o103W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 313) (codeMat 110) (codeMat 1) = codeMat 2 := by
      unfold actionA; rw [step113_415s51_QtInv]
      show (codeMat 313 : Mat3).transpose * codeMat 1 * (codeMat 444 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row51_qr : QuotientRankAtLeast step113_415ActualSource51 15 := by
  have hP : Invertible (codeMat 313 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 110 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 313) (codeMat 110) o103W_mono) 15 :=
    @quotientRankAtLeast_action (codeMat 313) (codeMat 110) hP hQ o103W_mono 15 QiushiMatmul.orbit103_lb15_mono
  exact quotientRankAtLeast_mono step113_415s51_source_le hAct

-- Source 52: row 238, orbit 134, lb 15, cap 1
def step113_415ActualSource52 : Submodule F2 Mat3 := spanCodes [273, 176, 120, 4, 2]

theorem step113_415_row52_W_le_source : o415W ≤ step113_415ActualSource52 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource52
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 176, 120, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 176, 120, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 176, 120, 4, 2] 2 (by decide)

private theorem step113_415s52_QtInv :
    (codeMat 85 : Mat3).transpose⁻¹ = (codeMat 340 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 85 : Mat3).transpose * (codeMat 340 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s52_source_le :
    step113_415ActualSource52 ≤ actionW (codeMat 185) (codeMat 85) o134W_mono := by
  apply step113_415_spanCodes_le_of_gens [273, 176, 120, 4, 2]
    (actionW (codeMat 185) (codeMat 85) o134W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 204 ∈ o134W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [156, 80, 32, 2, 1] 204 (by decide)
    have hact : actionA (codeMat 185) (codeMat 85) (codeMat 204) = codeMat 273 := by
      unfold actionA; rw [step113_415s52_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 204 * (codeMat 340 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 82 ∈ o134W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [156, 80, 32, 2, 1] 82 (by decide)
    have hact : actionA (codeMat 185) (codeMat 85) (codeMat 82) = codeMat 176 := by
      unfold actionA; rw [step113_415s52_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 82 * (codeMat 340 : Mat3).transpose = codeMat 176
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 237 ∈ o134W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [156, 80, 32, 2, 1] 237 (by decide)
    have hact : actionA (codeMat 185) (codeMat 85) (codeMat 237) = codeMat 120 := by
      unfold actionA; rw [step113_415s52_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 237 * (codeMat 340 : Mat3).transpose = codeMat 120
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o134W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [156, 80, 32, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 185) (codeMat 85) (codeMat 1) = codeMat 4 := by
      unfold actionA; rw [step113_415s52_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 1 * (codeMat 340 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o134W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [156, 80, 32, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 185) (codeMat 85) (codeMat 2) = codeMat 2 := by
      unfold actionA; rw [step113_415s52_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 2 * (codeMat 340 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row52_qr : QuotientRankAtLeast step113_415ActualSource52 15 := by
  have hP : Invertible (codeMat 185 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 85 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 185) (codeMat 85) o134W_mono) 15 :=
    @quotientRankAtLeast_action (codeMat 185) (codeMat 85) hP hQ o134W_mono 15 QiushiMatmul.orbit134_lb15_mono
  exact quotientRankAtLeast_mono step113_415s52_source_le hAct

-- Source 53: row 286, orbit 141, lb 15, cap 1
def step113_415ActualSource53 : Submodule F2 Mat3 := spanCodes [273, 88, 40, 4, 2]

theorem step113_415_row53_W_le_source : o415W ≤ step113_415ActualSource53 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource53
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 88, 40, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 88, 40, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 88, 40, 4, 2] 2 (by decide)

private theorem step113_415s53_QtInv :
    (codeMat 85 : Mat3).transpose⁻¹ = (codeMat 340 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 85 : Mat3).transpose * (codeMat 340 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s53_source_le :
    step113_415ActualSource53 ≤ actionW (codeMat 337) (codeMat 85) o141W_wc := by
  apply step113_415_spanCodes_le_of_gens [273, 88, 40, 4, 2]
    (actionW (codeMat 337) (codeMat 85) o141W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 84 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 84 (by decide)
    have hact : actionA (codeMat 337) (codeMat 85) (codeMat 84) = codeMat 273 := by
      unfold actionA; rw [step113_415s53_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 84 * (codeMat 340 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 381 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 381 (by decide)
    have hact : actionA (codeMat 337) (codeMat 85) (codeMat 381) = codeMat 88 := by
      unfold actionA; rw [step113_415s53_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 381 * (codeMat 340 : Mat3).transpose = codeMat 88
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 32 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 337) (codeMat 85) (codeMat 32) = codeMat 40 := by
      unfold actionA; rw [step113_415s53_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 32 * (codeMat 340 : Mat3).transpose = codeMat 40
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 337) (codeMat 85) (codeMat 1) = codeMat 4 := by
      unfold actionA; rw [step113_415s53_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 1 * (codeMat 340 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 337) (codeMat 85) (codeMat 2) = codeMat 2 := by
      unfold actionA; rw [step113_415s53_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 2 * (codeMat 340 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row53_qr : QuotientRankAtLeast step113_415ActualSource53 15 := by
  have hP : Invertible (codeMat 337 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 85 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 337) (codeMat 85) o141W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 337) (codeMat 85) hP hQ o141W_wc 15 QiushiMatmul.step109_orbit141_lb15_wc
  exact quotientRankAtLeast_mono step113_415s53_source_le hAct

-- Source 54: row 301, orbit 141, lb 15, cap 1
def step113_415ActualSource54 : Submodule F2 Mat3 := spanCodes [273, 185, 104, 4, 2]

theorem step113_415_row54_W_le_source : o415W ≤ step113_415ActualSource54 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource54
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 185, 104, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 185, 104, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 185, 104, 4, 2] 2 (by decide)

private theorem step113_415s54_QtInv :
    (codeMat 107 : Mat3).transpose⁻¹ = (codeMat 428 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 107 : Mat3).transpose * (codeMat 428 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s54_source_le :
    step113_415ActualSource54 ≤ actionW (codeMat 225) (codeMat 107) o141W_wc := by
  apply step113_415_spanCodes_le_of_gens [273, 185, 104, 4, 2]
    (actionW (codeMat 225) (codeMat 107) o141W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 86 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 86 (by decide)
    have hact : actionA (codeMat 225) (codeMat 107) (codeMat 86) = codeMat 273 := by
      unfold actionA; rw [step113_415s54_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 86 * (codeMat 428 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 267 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 267 (by decide)
    have hact : actionA (codeMat 225) (codeMat 107) (codeMat 267) = codeMat 185 := by
      unfold actionA; rw [step113_415s54_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 267 * (codeMat 428 : Mat3).transpose = codeMat 185
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 381 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 381 (by decide)
    have hact : actionA (codeMat 225) (codeMat 107) (codeMat 381) = codeMat 104 := by
      unfold actionA; rw [step113_415s54_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 381 * (codeMat 428 : Mat3).transpose = codeMat 104
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 225) (codeMat 107) (codeMat 2) = codeMat 4 := by
      unfold actionA; rw [step113_415s54_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 2 * (codeMat 428 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 225) (codeMat 107) (codeMat 1) = codeMat 2 := by
      unfold actionA; rw [step113_415s54_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 1 * (codeMat 428 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row54_qr : QuotientRankAtLeast step113_415ActualSource54 15 := by
  have hP : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 107 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 225) (codeMat 107) o141W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 225) (codeMat 107) hP hQ o141W_wc 15 QiushiMatmul.step109_orbit141_lb15_wc
  exact quotientRankAtLeast_mono step113_415s54_source_le hAct

-- Source 55: row 314, orbit 141, lb 15, cap 1
def step113_415ActualSource55 : Submodule F2 Mat3 := spanCodes [273, 136, 120, 4, 2]

theorem step113_415_row55_W_le_source : o415W ≤ step113_415ActualSource55 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource55
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 136, 120, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 136, 120, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 136, 120, 4, 2] 2 (by decide)

private theorem step113_415s55_QtInv :
    (codeMat 122 : Mat3).transpose⁻¹ = (codeMat 460 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 122 : Mat3).transpose * (codeMat 460 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s55_source_le :
    step113_415ActualSource55 ≤ actionW (codeMat 249) (codeMat 122) o141W_wc := by
  apply step113_415_spanCodes_le_of_gens [273, 136, 120, 4, 2]
    (actionW (codeMat 249) (codeMat 122) o141W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 85 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 85 (by decide)
    have hact : actionA (codeMat 249) (codeMat 122) (codeMat 85) = codeMat 273 := by
      unfold actionA; rw [step113_415s55_QtInv]
      show (codeMat 249 : Mat3).transpose * codeMat 85 * (codeMat 460 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 350 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 350 (by decide)
    have hact : actionA (codeMat 249) (codeMat 122) (codeMat 350) = codeMat 136 := by
      unfold actionA; rw [step113_415s55_QtInv]
      show (codeMat 249 : Mat3).transpose * codeMat 350 * (codeMat 460 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 119 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 119 (by decide)
    have hact : actionA (codeMat 249) (codeMat 122) (codeMat 119) = codeMat 120 := by
      unfold actionA; rw [step113_415s55_QtInv]
      show (codeMat 249 : Mat3).transpose * codeMat 119 * (codeMat 460 : Mat3).transpose = codeMat 120
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 249) (codeMat 122) (codeMat 2) = codeMat 4 := by
      unfold actionA; rw [step113_415s55_QtInv]
      show (codeMat 249 : Mat3).transpose * codeMat 2 * (codeMat 460 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 249) (codeMat 122) (codeMat 3) = codeMat 2 := by
      unfold actionA; rw [step113_415s55_QtInv]
      show (codeMat 249 : Mat3).transpose * codeMat 3 * (codeMat 460 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row55_qr : QuotientRankAtLeast step113_415ActualSource55 15 := by
  have hP : Invertible (codeMat 249 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 122 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 249) (codeMat 122) o141W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 249) (codeMat 122) hP hQ o141W_wc 15 QiushiMatmul.step109_orbit141_lb15_wc
  exact quotientRankAtLeast_mono step113_415s55_source_le hAct

-- Source 56: row 319, orbit 141, lb 15, cap 1
def step113_415ActualSource56 : Submodule F2 Mat3 := spanCodes [273, 137, 120, 4, 2]

theorem step113_415_row56_W_le_source : o415W ≤ step113_415ActualSource56 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource56
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 137, 120, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 137, 120, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 137, 120, 4, 2] 2 (by decide)

private theorem step113_415s56_QtInv :
    (codeMat 122 : Mat3).transpose⁻¹ = (codeMat 460 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 122 : Mat3).transpose * (codeMat 460 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s56_source_le :
    step113_415ActualSource56 ≤ actionW (codeMat 185) (codeMat 122) o141W_wc := by
  apply step113_415_spanCodes_le_of_gens [273, 137, 120, 4, 2]
    (actionW (codeMat 185) (codeMat 122) o141W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 84 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 84 (by decide)
    have hact : actionA (codeMat 185) (codeMat 122) (codeMat 84) = codeMat 273 := by
      unfold actionA; rw [step113_415s56_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 84 * (codeMat 460 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 349 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 349 (by decide)
    have hact : actionA (codeMat 185) (codeMat 122) (codeMat 349) = codeMat 137 := by
      unfold actionA; rw [step113_415s56_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 349 * (codeMat 460 : Mat3).transpose = codeMat 137
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 118 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 118 (by decide)
    have hact : actionA (codeMat 185) (codeMat 122) (codeMat 118) = codeMat 120 := by
      unfold actionA; rw [step113_415s56_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 118 * (codeMat 460 : Mat3).transpose = codeMat 120
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 185) (codeMat 122) (codeMat 2) = codeMat 4 := by
      unfold actionA; rw [step113_415s56_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 2 * (codeMat 460 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 185) (codeMat 122) (codeMat 3) = codeMat 2 := by
      unfold actionA; rw [step113_415s56_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 3 * (codeMat 460 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row56_qr : QuotientRankAtLeast step113_415ActualSource56 15 := by
  have hP : Invertible (codeMat 185 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 122 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 185) (codeMat 122) o141W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 185) (codeMat 122) hP hQ o141W_wc 15 QiushiMatmul.step109_orbit141_lb15_wc
  exact quotientRankAtLeast_mono step113_415s56_source_le hAct

-- Source 57: row 322, orbit 141, lb 15, cap 1
def step113_415ActualSource57 : Submodule F2 Mat3 := spanCodes [273, 168, 80, 4, 2]

theorem step113_415_row57_W_le_source : o415W ≤ step113_415ActualSource57 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource57
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 168, 80, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 168, 80, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 168, 80, 4, 2] 2 (by decide)

private theorem step113_415s57_QtInv :
    (codeMat 106 : Mat3).transpose⁻¹ = (codeMat 396 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 106 : Mat3).transpose * (codeMat 396 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s57_source_le :
    step113_415ActualSource57 ≤ actionW (codeMat 169) (codeMat 106) o141W_wc := by
  apply step113_415_spanCodes_le_of_gens [273, 168, 80, 4, 2]
    (actionW (codeMat 169) (codeMat 106) o141W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 84 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 84 (by decide)
    have hact : actionA (codeMat 169) (codeMat 106) (codeMat 84) = codeMat 273 := by
      unfold actionA; rw [step113_415s57_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 84 * (codeMat 396 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 265 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 265 (by decide)
    have hact : actionA (codeMat 169) (codeMat 106) (codeMat 265) = codeMat 168 := by
      unfold actionA; rw [step113_415s57_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 265 * (codeMat 396 : Mat3).transpose = codeMat 168
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 118 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 118 (by decide)
    have hact : actionA (codeMat 169) (codeMat 106) (codeMat 118) = codeMat 80 := by
      unfold actionA; rw [step113_415s57_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 118 * (codeMat 396 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 169) (codeMat 106) (codeMat 2) = codeMat 4 := by
      unfold actionA; rw [step113_415s57_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 2 * (codeMat 396 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 106) (codeMat 1) = codeMat 2 := by
      unfold actionA; rw [step113_415s57_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * (codeMat 396 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row57_qr : QuotientRankAtLeast step113_415ActualSource57 15 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 106 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 106) o141W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 106) hP hQ o141W_wc 15 QiushiMatmul.step109_orbit141_lb15_wc
  exact quotientRankAtLeast_mono step113_415s57_source_le hAct

-- Source 58: row 323, orbit 141, lb 15, cap 1
def step113_415ActualSource58 : Submodule F2 Mat3 := spanCodes [273, 169, 81, 4, 2]

theorem step113_415_row58_W_le_source : o415W ≤ step113_415ActualSource58 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource58
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 169, 81, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 169, 81, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 169, 81, 4, 2] 2 (by decide)

private theorem step113_415s58_QtInv :
    (codeMat 106 : Mat3).transpose⁻¹ = (codeMat 396 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 106 : Mat3).transpose * (codeMat 396 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s58_source_le :
    step113_415ActualSource58 ≤ actionW (codeMat 225) (codeMat 106) o141W_wc := by
  apply step113_415_spanCodes_le_of_gens [273, 169, 81, 4, 2]
    (actionW (codeMat 225) (codeMat 106) o141W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 87 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 87 (by decide)
    have hact : actionA (codeMat 225) (codeMat 106) (codeMat 87) = codeMat 273 := by
      unfold actionA; rw [step113_415s58_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 87 * (codeMat 396 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 266 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 266 (by decide)
    have hact : actionA (codeMat 225) (codeMat 106) (codeMat 266) = codeMat 169 := by
      unfold actionA; rw [step113_415s58_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 266 * (codeMat 396 : Mat3).transpose = codeMat 169
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 119 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 119 (by decide)
    have hact : actionA (codeMat 225) (codeMat 106) (codeMat 119) = codeMat 81 := by
      unfold actionA; rw [step113_415s58_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 119 * (codeMat 396 : Mat3).transpose = codeMat 81
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 225) (codeMat 106) (codeMat 2) = codeMat 4 := by
      unfold actionA; rw [step113_415s58_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 2 * (codeMat 396 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 225) (codeMat 106) (codeMat 1) = codeMat 2 := by
      unfold actionA; rw [step113_415s58_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 1 * (codeMat 396 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row58_qr : QuotientRankAtLeast step113_415ActualSource58 15 := by
  have hP : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 106 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 225) (codeMat 106) o141W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 225) (codeMat 106) hP hQ o141W_wc 15 QiushiMatmul.step109_orbit141_lb15_wc
  exact quotientRankAtLeast_mono step113_415s58_source_le hAct

-- Source 59: row 442, orbit 144, lb 15, cap 1
def step113_415ActualSource59 : Submodule F2 Mat3 := spanCodes [273, 88, 56, 4, 2]

theorem step113_415_row59_W_le_source : o415W ≤ step113_415ActualSource59 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource59
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 88, 56, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 88, 56, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 88, 56, 4, 2] 2 (by decide)

private theorem step113_415s59_QtInv :
    (codeMat 93 : Mat3).transpose⁻¹ = (codeMat 372 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 93 : Mat3).transpose * (codeMat 372 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s59_source_le :
    step113_415ActualSource59 ≤ actionW (codeMat 337) (codeMat 93) o144W := by
  apply step113_415_spanCodes_le_of_gens [273, 88, 56, 4, 2]
    (actionW (codeMat 337) (codeMat 93) o144W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 86 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 86 (by decide)
    have hact : actionA (codeMat 337) (codeMat 93) (codeMat 86) = codeMat 273 := by
      unfold actionA; rw [step113_415s59_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 86 * (codeMat 372 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 495 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 495 (by decide)
    have hact : actionA (codeMat 337) (codeMat 93) (codeMat 495) = codeMat 88 := by
      unfold actionA; rw [step113_415s59_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 495 * (codeMat 372 : Mat3).transpose = codeMat 88
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 32 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 337) (codeMat 93) (codeMat 32) = codeMat 56 := by
      unfold actionA; rw [step113_415s59_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 32 * (codeMat 372 : Mat3).transpose = codeMat 56
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 337) (codeMat 93) (codeMat 1) = codeMat 4 := by
      unfold actionA; rw [step113_415s59_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 1 * (codeMat 372 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 337) (codeMat 93) (codeMat 2) = codeMat 2 := by
      unfold actionA; rw [step113_415s59_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 2 * (codeMat 372 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row59_qr : QuotientRankAtLeast step113_415ActualSource59 15 := by
  have hP : Invertible (codeMat 337 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 93 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 337) (codeMat 93) o144W) 15 :=
    @quotientRankAtLeast_action (codeMat 337) (codeMat 93) hP hQ o144W 15 QiushiMatmul.step99_orbit144_lb15_unconditional
  exact quotientRankAtLeast_mono step113_415s59_source_le hAct

-- Source 60: row 444, orbit 144, lb 15, cap 1
def step113_415ActualSource60 : Submodule F2 Mat3 := spanCodes [273, 88, 57, 4, 2]

theorem step113_415_row60_W_le_source : o415W ≤ step113_415ActualSource60 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource60
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 88, 57, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 88, 57, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 88, 57, 4, 2] 2 (by decide)

private theorem step113_415s60_QtInv :
    (codeMat 93 : Mat3).transpose⁻¹ = (codeMat 372 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 93 : Mat3).transpose * (codeMat 372 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s60_source_le :
    step113_415ActualSource60 ≤ actionW (codeMat 281) (codeMat 93) o144W := by
  apply step113_415_spanCodes_le_of_gens [273, 88, 57, 4, 2]
    (actionW (codeMat 281) (codeMat 93) o144W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 85 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 85 (by decide)
    have hact : actionA (codeMat 281) (codeMat 93) (codeMat 85) = codeMat 273 := by
      unfold actionA; rw [step113_415s60_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 85 * (codeMat 372 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 493 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 493 (by decide)
    have hact : actionA (codeMat 281) (codeMat 93) (codeMat 493) = codeMat 88 := by
      unfold actionA; rw [step113_415s60_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 493 * (codeMat 372 : Mat3).transpose = codeMat 88
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 35 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 35 (by decide)
    have hact : actionA (codeMat 281) (codeMat 93) (codeMat 35) = codeMat 57 := by
      unfold actionA; rw [step113_415s60_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 35 * (codeMat 372 : Mat3).transpose = codeMat 57
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 281) (codeMat 93) (codeMat 1) = codeMat 4 := by
      unfold actionA; rw [step113_415s60_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 1 * (codeMat 372 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 281) (codeMat 93) (codeMat 2) = codeMat 2 := by
      unfold actionA; rw [step113_415s60_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 2 * (codeMat 372 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row60_qr : QuotientRankAtLeast step113_415ActualSource60 15 := by
  have hP : Invertible (codeMat 281 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 93 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 281) (codeMat 93) o144W) 15 :=
    @quotientRankAtLeast_action (codeMat 281) (codeMat 93) hP hQ o144W 15 QiushiMatmul.step99_orbit144_lb15_unconditional
  exact quotientRankAtLeast_mono step113_415s60_source_le hAct

-- Source 61: row 453, orbit 144, lb 15, cap 1
def step113_415ActualSource61 : Submodule F2 Mat3 := spanCodes [273, 169, 104, 4, 2]

theorem step113_415_row61_W_le_source : o415W ≤ step113_415ActualSource61 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource61
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 169, 104, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 169, 104, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 169, 104, 4, 2] 2 (by decide)

private theorem step113_415s61_QtInv :
    (codeMat 99 : Mat3).transpose⁻¹ = (codeMat 172 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 99 : Mat3).transpose * (codeMat 172 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s61_source_le :
    step113_415ActualSource61 ≤ actionW (codeMat 169) (codeMat 99) o144W := by
  apply step113_415_spanCodes_le_of_gens [273, 169, 104, 4, 2]
    (actionW (codeMat 169) (codeMat 99) o144W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 87 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 87 (by decide)
    have hact : actionA (codeMat 169) (codeMat 99) (codeMat 87) = codeMat 273 := by
      unfold actionA; rw [step113_415s61_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 87 * (codeMat 172 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 460 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 460 (by decide)
    have hact : actionA (codeMat 169) (codeMat 99) (codeMat 460) = codeMat 169 := by
      unfold actionA; rw [step113_415s61_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 460 * (codeMat 172 : Mat3).transpose = codeMat 169
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 493 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 493 (by decide)
    have hact : actionA (codeMat 169) (codeMat 99) (codeMat 493) = codeMat 104 := by
      unfold actionA; rw [step113_415s61_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 493 * (codeMat 172 : Mat3).transpose = codeMat 104
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 169) (codeMat 99) (codeMat 2) = codeMat 4 := by
      unfold actionA; rw [step113_415s61_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 2 * (codeMat 172 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 99) (codeMat 1) = codeMat 2 := by
      unfold actionA; rw [step113_415s61_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * (codeMat 172 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row61_qr : QuotientRankAtLeast step113_415ActualSource61 15 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 99 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 99) o144W) 15 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 99) hP hQ o144W 15 QiushiMatmul.step99_orbit144_lb15_unconditional
  exact quotientRankAtLeast_mono step113_415s61_source_le hAct

-- Source 62: row 466, orbit 144, lb 15, cap 1
def step113_415ActualSource62 : Submodule F2 Mat3 := spanCodes [273, 152, 120, 4, 2]

theorem step113_415_row62_W_le_source : o415W ≤ step113_415ActualSource62 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource62
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 152, 120, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 152, 120, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 152, 120, 4, 2] 2 (by decide)

private theorem step113_415s62_QtInv :
    (codeMat 122 : Mat3).transpose⁻¹ = (codeMat 460 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 122 : Mat3).transpose * (codeMat 460 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s62_source_le :
    step113_415ActualSource62 ≤ actionW (codeMat 185) (codeMat 122) o144W := by
  apply step113_415_spanCodes_le_of_gens [273, 152, 120, 4, 2]
    (actionW (codeMat 185) (codeMat 122) o144W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 84 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 84 (by decide)
    have hact : actionA (codeMat 185) (codeMat 122) (codeMat 84) = codeMat 273 := by
      unfold actionA; rw [step113_415s62_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 84 * (codeMat 460 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 411 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 411 (by decide)
    have hact : actionA (codeMat 185) (codeMat 122) (codeMat 411) = codeMat 152 := by
      unfold actionA; rw [step113_415s62_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 411 * (codeMat 460 : Mat3).transpose = codeMat 152
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 118 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 118 (by decide)
    have hact : actionA (codeMat 185) (codeMat 122) (codeMat 118) = codeMat 120 := by
      unfold actionA; rw [step113_415s62_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 118 * (codeMat 460 : Mat3).transpose = codeMat 120
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 185) (codeMat 122) (codeMat 2) = codeMat 4 := by
      unfold actionA; rw [step113_415s62_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 2 * (codeMat 460 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 185) (codeMat 122) (codeMat 3) = codeMat 2 := by
      unfold actionA; rw [step113_415s62_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 3 * (codeMat 460 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row62_qr : QuotientRankAtLeast step113_415ActualSource62 15 := by
  have hP : Invertible (codeMat 185 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 122 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 185) (codeMat 122) o144W) 15 :=
    @quotientRankAtLeast_action (codeMat 185) (codeMat 122) hP hQ o144W 15 QiushiMatmul.step99_orbit144_lb15_unconditional
  exact quotientRankAtLeast_mono step113_415s62_source_le hAct

-- Source 63: row 471, orbit 144, lb 15, cap 1
def step113_415ActualSource63 : Submodule F2 Mat3 := spanCodes [273, 153, 120, 4, 2]

theorem step113_415_row63_W_le_source : o415W ≤ step113_415ActualSource63 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource63
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 153, 120, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 153, 120, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 153, 120, 4, 2] 2 (by decide)

private theorem step113_415s63_QtInv :
    (codeMat 122 : Mat3).transpose⁻¹ = (codeMat 460 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 122 : Mat3).transpose * (codeMat 460 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s63_source_le :
    step113_415ActualSource63 ≤ actionW (codeMat 249) (codeMat 122) o144W := by
  apply step113_415_spanCodes_le_of_gens [273, 153, 120, 4, 2]
    (actionW (codeMat 249) (codeMat 122) o144W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 85 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 85 (by decide)
    have hact : actionA (codeMat 249) (codeMat 122) (codeMat 85) = codeMat 273 := by
      unfold actionA; rw [step113_415s63_QtInv]
      show (codeMat 249 : Mat3).transpose * codeMat 85 * (codeMat 460 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 411 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 411 (by decide)
    have hact : actionA (codeMat 249) (codeMat 122) (codeMat 411) = codeMat 153 := by
      unfold actionA; rw [step113_415s63_QtInv]
      show (codeMat 249 : Mat3).transpose * codeMat 411 * (codeMat 460 : Mat3).transpose = codeMat 153
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 119 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 119 (by decide)
    have hact : actionA (codeMat 249) (codeMat 122) (codeMat 119) = codeMat 120 := by
      unfold actionA; rw [step113_415s63_QtInv]
      show (codeMat 249 : Mat3).transpose * codeMat 119 * (codeMat 460 : Mat3).transpose = codeMat 120
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 249) (codeMat 122) (codeMat 2) = codeMat 4 := by
      unfold actionA; rw [step113_415s63_QtInv]
      show (codeMat 249 : Mat3).transpose * codeMat 2 * (codeMat 460 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 249) (codeMat 122) (codeMat 3) = codeMat 2 := by
      unfold actionA; rw [step113_415s63_QtInv]
      show (codeMat 249 : Mat3).transpose * codeMat 3 * (codeMat 460 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row63_qr : QuotientRankAtLeast step113_415ActualSource63 15 := by
  have hP : Invertible (codeMat 249 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 122 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 249) (codeMat 122) o144W) 15 :=
    @quotientRankAtLeast_action (codeMat 249) (codeMat 122) hP hQ o144W 15 QiushiMatmul.step99_orbit144_lb15_unconditional
  exact quotientRankAtLeast_mono step113_415s63_source_le hAct

-- Source 64: row 482, orbit 144, lb 15, cap 1
def step113_415ActualSource64 : Submodule F2 Mat3 := spanCodes [273, 184, 64, 4, 2]

theorem step113_415_row64_W_le_source : o415W ≤ step113_415ActualSource64 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource64
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 184, 64, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 184, 64, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 184, 64, 4, 2] 2 (by decide)

private theorem step113_415s64_QtInv :
    (codeMat 98 : Mat3).transpose⁻¹ = (codeMat 140 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 98 : Mat3).transpose * (codeMat 140 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s64_source_le :
    step113_415ActualSource64 ≤ actionW (codeMat 225) (codeMat 98) o144W := by
  apply step113_415_spanCodes_le_of_gens [273, 184, 64, 4, 2]
    (actionW (codeMat 225) (codeMat 98) o144W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 85 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 85 (by decide)
    have hact : actionA (codeMat 225) (codeMat 98) (codeMat 85) = codeMat 273 := by
      unfold actionA; rw [step113_415s64_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 85 * (codeMat 140 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 463 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 463 (by decide)
    have hact : actionA (codeMat 225) (codeMat 98) (codeMat 463) = codeMat 184 := by
      unfold actionA; rw [step113_415s64_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 463 * (codeMat 140 : Mat3).transpose = codeMat 184
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 32 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 225) (codeMat 98) (codeMat 32) = codeMat 64 := by
      unfold actionA; rw [step113_415s64_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 32 * (codeMat 140 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 225) (codeMat 98) (codeMat 2) = codeMat 4 := by
      unfold actionA; rw [step113_415s64_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 2 * (codeMat 140 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 225) (codeMat 98) (codeMat 1) = codeMat 2 := by
      unfold actionA; rw [step113_415s64_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 1 * (codeMat 140 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row64_qr : QuotientRankAtLeast step113_415ActualSource64 15 := by
  have hP : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 225) (codeMat 98) o144W) 15 :=
    @quotientRankAtLeast_action (codeMat 225) (codeMat 98) hP hQ o144W 15 QiushiMatmul.step99_orbit144_lb15_unconditional
  exact quotientRankAtLeast_mono step113_415s64_source_le hAct

-- Source 65: row 725, orbit 29, lb 15, cap 1
def step113_415ActualSource65 : Submodule F2 Mat3 := spanCodes [257, 136, 32, 16, 4, 2]

theorem step113_415_row65_W_le_source : o415W ≤ step113_415ActualSource65 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource65
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [257, 136, 32, 16, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [257, 136, 32, 16, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [257, 136, 32, 16, 4, 2] 2 (by decide)

private theorem step113_415s65_QtInv :
    (codeMat 98 : Mat3).transpose⁻¹ = (codeMat 140 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 98 : Mat3).transpose * (codeMat 140 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s65_source_le :
    step113_415ActualSource65 ≤ actionW (codeMat 266) (codeMat 98) orbit29W := by
  apply step113_415_spanCodes_le_of_gens [257, 136, 32, 16, 4, 2]
    (actionW (codeMat 266) (codeMat 98) orbit29W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 160 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 160 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 160) = codeMat 257 := by
      unfold actionA; rw [step113_415s65_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 160 * (codeMat 140 : Mat3).transpose = codeMat 257
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 68 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 68 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 68) = codeMat 136 := by
      unfold actionA; rw [step113_415s65_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 68 * (codeMat 140 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 2) = codeMat 32 := by
      unfold actionA; rw [step113_415s65_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 140 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 1) = codeMat 16 := by
      unfold actionA; rw [step113_415s65_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 140 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 16 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 16) = codeMat 4 := by
      unfold actionA; rw [step113_415s65_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 140 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 8) = codeMat 2 := by
      unfold actionA; rw [step113_415s65_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 140 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row65_qr : QuotientRankAtLeast step113_415ActualSource65 15 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 98) orbit29W) 15 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 98) hP hQ orbit29W 15 QiushiMatmul.orbit29_lb15
  exact quotientRankAtLeast_mono step113_415s65_source_le hAct

-- Source 66: row 785, orbit 35, lb 15, cap 1
def step113_415ActualSource66 : Submodule F2 Mat3 := spanCodes [273, 144, 89, 33, 4, 2]

theorem step113_415_row66_W_le_source : o415W ≤ step113_415ActualSource66 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource66
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 144, 89, 33, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 144, 89, 33, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 144, 89, 33, 4, 2] 2 (by decide)

private theorem step113_415s66_QtInv :
    (codeMat 419 : Mat3).transpose⁻¹ = (codeMat 183 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 419 : Mat3).transpose * (codeMat 183 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s66_source_le :
    step113_415ActualSource66 ≤ transposeW (actionW (codeMat 354) (codeMat 419) orbit35W) := by
  apply step113_415_spanCodes_le_of_gens [273, 144, 89, 33, 4, 2]
    (transposeW (actionW (codeMat 354) (codeMat 419) orbit35W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 125 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 125 (by decide)
    have hact : actionA (codeMat 354) (codeMat 419) (codeMat 125) = codeMat 273 := by
      unfold actionA; rw [step113_415s66_QtInv]
      show (codeMat 354 : Mat3).transpose * codeMat 125 * (codeMat 183 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 273 ∈ actionW (codeMat 354) (codeMat 419) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 273 : Mat3).transpose = codeMat 273 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h1
    have hw : codeMat 3 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 3 (by decide)
    have hact : actionA (codeMat 354) (codeMat 419) (codeMat 3) = codeMat 48 := by
      unfold actionA; rw [step113_415s66_QtInv]
      show (codeMat 354 : Mat3).transpose * codeMat 3 * (codeMat 183 : Mat3).transpose = codeMat 48
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 48 ∈ actionW (codeMat 354) (codeMat 419) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 48 : Mat3).transpose = codeMat 144 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h2
    have hw : codeMat 149 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 149 (by decide)
    have hact : actionA (codeMat 354) (codeMat 419) (codeMat 149) = codeMat 23 := by
      unfold actionA; rw [step113_415s66_QtInv]
      show (codeMat 354 : Mat3).transpose * codeMat 149 * (codeMat 183 : Mat3).transpose = codeMat 23
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 23 ∈ actionW (codeMat 354) (codeMat 419) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 23 : Mat3).transpose = codeMat 89 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h3
    have hw : codeMat 96 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 96 (by decide)
    have hact : actionA (codeMat 354) (codeMat 419) (codeMat 96) = codeMat 129 := by
      unfold actionA; rw [step113_415s66_QtInv]
      show (codeMat 354 : Mat3).transpose * codeMat 96 * (codeMat 183 : Mat3).transpose = codeMat 129
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 129 ∈ actionW (codeMat 354) (codeMat 419) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 129 : Mat3).transpose = codeMat 33 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h4
    have hw : codeMat 8 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 8 (by decide)
    have hact : actionA (codeMat 354) (codeMat 419) (codeMat 8) = codeMat 64 := by
      unfold actionA; rw [step113_415s66_QtInv]
      show (codeMat 354 : Mat3).transpose * codeMat 8 * (codeMat 183 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 64 ∈ actionW (codeMat 354) (codeMat 419) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 64 : Mat3).transpose = codeMat 4 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h5
    have hw : codeMat 1 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 1 (by decide)
    have hact : actionA (codeMat 354) (codeMat 419) (codeMat 1) = codeMat 8 := by
      unfold actionA; rw [step113_415s66_QtInv]
      show (codeMat 354 : Mat3).transpose * codeMat 1 * (codeMat 183 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 8 ∈ actionW (codeMat 354) (codeMat 419) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 8 : Mat3).transpose = codeMat 2 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans

theorem step113_415_row66_qr : QuotientRankAtLeast step113_415ActualSource66 15 := by
  have hP : Invertible (codeMat 354 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 419 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 354) (codeMat 419) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 354) (codeMat 419) hP hQ orbit35W 15 QiushiMatmul.orbit35_lb15
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 354) (codeMat 419) orbit35W)) 15 :=
    quotientRankAtLeast_transpose hAct
  exact quotientRankAtLeast_mono step113_415s66_source_le hT

-- Source 67: row 802, orbit 35, lb 15, cap 1
def step113_415ActualSource67 : Submodule F2 Mat3 := spanCodes [273, 129, 73, 49, 4, 2]

theorem step113_415_row67_W_le_source : o415W ≤ step113_415ActualSource67 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource67
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 129, 73, 49, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 129, 73, 49, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 129, 73, 49, 4, 2] 2 (by decide)

private theorem step113_415s67_QtInv :
    (codeMat 403 : Mat3).transpose⁻¹ = (codeMat 403 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 403 : Mat3).transpose * (codeMat 403 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s67_source_le :
    step113_415ActualSource67 ≤ transposeW (actionW (codeMat 84) (codeMat 403) orbit35W) := by
  apply step113_415_spanCodes_le_of_gens [273, 129, 73, 49, 4, 2]
    (transposeW (actionW (codeMat 84) (codeMat 403) orbit35W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 124 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 124 (by decide)
    have hact : actionA (codeMat 84) (codeMat 403) (codeMat 124) = codeMat 273 := by
      unfold actionA; rw [step113_415s67_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 124 * (codeMat 403 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 273 ∈ actionW (codeMat 84) (codeMat 403) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 273 : Mat3).transpose = codeMat 273 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h1
    have hw : codeMat 96 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 96 (by decide)
    have hact : actionA (codeMat 84) (codeMat 403) (codeMat 96) = codeMat 33 := by
      unfold actionA; rw [step113_415s67_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 96 * (codeMat 403 : Mat3).transpose = codeMat 33
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 33 ∈ actionW (codeMat 84) (codeMat 403) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 33 : Mat3).transpose = codeMat 129 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h2
    have hw : codeMat 128 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 403) (codeMat 128) = codeMat 7 := by
      unfold actionA; rw [step113_415s67_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 403 : Mat3).transpose = codeMat 7
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 7 ∈ actionW (codeMat 84) (codeMat 403) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 7 : Mat3).transpose = codeMat 73 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h3
    have hw : codeMat 127 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 127 (by decide)
    have hact : actionA (codeMat 84) (codeMat 403) (codeMat 127) = codeMat 145 := by
      unfold actionA; rw [step113_415s67_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 127 * (codeMat 403 : Mat3).transpose = codeMat 145
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 145 ∈ actionW (codeMat 84) (codeMat 403) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 145 : Mat3).transpose = codeMat 49 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h4
    have hw : codeMat 1 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 403) (codeMat 1) = codeMat 64 := by
      unfold actionA; rw [step113_415s67_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 403 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 64 ∈ actionW (codeMat 84) (codeMat 403) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 64 : Mat3).transpose = codeMat 4 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h5
    have hw : codeMat 8 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 403) (codeMat 8) = codeMat 8 := by
      unfold actionA; rw [step113_415s67_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 403 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 8 ∈ actionW (codeMat 84) (codeMat 403) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 8 : Mat3).transpose = codeMat 2 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans

theorem step113_415_row67_qr : QuotientRankAtLeast step113_415ActualSource67 15 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 403 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 403) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 403) hP hQ orbit35W 15 QiushiMatmul.orbit35_lb15
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 84) (codeMat 403) orbit35W)) 15 :=
    quotientRankAtLeast_transpose hAct
  exact quotientRankAtLeast_mono step113_415s67_source_le hT

-- Source 68: row 1909, orbit 5, lb 9, cap 7
def step113_415ActualSource68 : Submodule F2 Mat3 := spanCodes [272, 64, 32, 8, 4, 2, 1]

theorem step113_415_row68_W_le_source : o415W ≤ step113_415ActualSource68 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource68
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 64, 32, 8, 4, 2, 1] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 64, 32, 8, 4, 2, 1] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 64, 32, 8, 4, 2, 1] 2 (by decide)

private theorem step113_415s68_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s68_source_le :
    step113_415ActualSource68 ≤ actionW (codeMat 273) (codeMat 161) orbit5W := by
  apply step113_415_spanCodes_le_of_gens [272, 64, 32, 8, 4, 2, 1]
    (actionW (codeMat 273) (codeMat 161) orbit5W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 160 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 160 (by decide)
    have hact : actionA (codeMat 273) (codeMat 161) (codeMat 160) = codeMat 272 := by
      unfold actionA; rw [step113_415s68_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 160 * (codeMat 161 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 64 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 64 (by decide)
    have hact : actionA (codeMat 273) (codeMat 161) (codeMat 64) = codeMat 64 := by
      unfold actionA; rw [step113_415s68_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 64 * (codeMat 161 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 16 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 16 (by decide)
    have hact : actionA (codeMat 273) (codeMat 161) (codeMat 16) = codeMat 32 := by
      unfold actionA; rw [step113_415s68_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 16 * (codeMat 161 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 161) (codeMat 8) = codeMat 8 := by
      unfold actionA; rw [step113_415s68_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 161 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 161) (codeMat 2) = codeMat 4 := by
      unfold actionA; rw [step113_415s68_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 161 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 4 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 4 (by decide)
    have hact : actionA (codeMat 273) (codeMat 161) (codeMat 4) = codeMat 2 := by
      unfold actionA; rw [step113_415s68_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 4 * (codeMat 161 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 1 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 161) (codeMat 1) = codeMat 1 := by
      unfold actionA; rw [step113_415s68_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row68_qr : QuotientRankAtLeast step113_415ActualSource68 9 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 161) orbit5W) 9 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 161) hP hQ orbit5W 9 QiushiMatmul.orbit5_lb9
  exact quotientRankAtLeast_mono step113_415s68_source_le hAct

-- Source 69: row 1910, orbit 5, lb 9, cap 7
def step113_415ActualSource69 : Submodule F2 Mat3 := spanCodes [272, 80, 32, 8, 4, 2, 1]

theorem step113_415_row69_W_le_source : o415W ≤ step113_415ActualSource69 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource69
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 80, 32, 8, 4, 2, 1] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 80, 32, 8, 4, 2, 1] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 80, 32, 8, 4, 2, 1] 2 (by decide)

private theorem step113_415s69_QtInv :
    (codeMat 169 : Mat3).transpose⁻¹ = (codeMat 225 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 169 : Mat3).transpose * (codeMat 225 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s69_source_le :
    step113_415ActualSource69 ≤ actionW (codeMat 273) (codeMat 169) orbit5W := by
  apply step113_415_spanCodes_le_of_gens [272, 80, 32, 8, 4, 2, 1]
    (actionW (codeMat 273) (codeMat 169) orbit5W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 160 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 160 (by decide)
    have hact : actionA (codeMat 273) (codeMat 169) (codeMat 160) = codeMat 272 := by
      unfold actionA; rw [step113_415s69_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 160 * (codeMat 225 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 224 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 224 (by decide)
    have hact : actionA (codeMat 273) (codeMat 169) (codeMat 224) = codeMat 80 := by
      unfold actionA; rw [step113_415s69_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 224 * (codeMat 225 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 16 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 16 (by decide)
    have hact : actionA (codeMat 273) (codeMat 169) (codeMat 16) = codeMat 32 := by
      unfold actionA; rw [step113_415s69_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 16 * (codeMat 225 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 24 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 24 (by decide)
    have hact : actionA (codeMat 273) (codeMat 169) (codeMat 24) = codeMat 8 := by
      unfold actionA; rw [step113_415s69_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 24 * (codeMat 225 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 169) (codeMat 2) = codeMat 4 := by
      unfold actionA; rw [step113_415s69_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 225 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 4 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 4 (by decide)
    have hact : actionA (codeMat 273) (codeMat 169) (codeMat 4) = codeMat 2 := by
      unfold actionA; rw [step113_415s69_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 4 * (codeMat 225 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 3 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 3 (by decide)
    have hact : actionA (codeMat 273) (codeMat 169) (codeMat 3) = codeMat 1 := by
      unfold actionA; rw [step113_415s69_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 3 * (codeMat 225 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row69_qr : QuotientRankAtLeast step113_415ActualSource69 9 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 169) orbit5W) 9 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 169) hP hQ orbit5W 9 QiushiMatmul.orbit5_lb9
  exact quotientRankAtLeast_mono step113_415s69_source_le hAct

-- Source 70: row 1962, orbit 7, lb 9, cap 7
def step113_415ActualSource70 : Submodule F2 Mat3 := spanCodes [264, 72, 32, 24, 4, 2, 1]

theorem step113_415_row70_W_le_source : o415W ≤ step113_415ActualSource70 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource70
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [264, 72, 32, 24, 4, 2, 1] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [264, 72, 32, 24, 4, 2, 1] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [264, 72, 32, 24, 4, 2, 1] 2 (by decide)

private theorem step113_415s70_QtInv :
    (codeMat 213 : Mat3).transpose⁻¹ = (codeMat 470 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 213 : Mat3).transpose * (codeMat 470 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s70_source_le :
    step113_415ActualSource70 ≤ actionW (codeMat 273) (codeMat 213) flatW_7 := by
  apply step113_415_spanCodes_le_of_gens [264, 72, 32, 24, 4, 2, 1]
    (actionW (codeMat 273) (codeMat 213) flatW_7)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 104 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 104 (by decide)
    have hact : actionA (codeMat 273) (codeMat 213) (codeMat 104) = codeMat 264 := by
      unfold actionA; rw [step113_415s70_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 104 * (codeMat 470 : Mat3).transpose = codeMat 264
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 360 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 360 (by decide)
    have hact : actionA (codeMat 273) (codeMat 213) (codeMat 360) = codeMat 72 := by
      unfold actionA; rw [step113_415s70_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 360 * (codeMat 470 : Mat3).transpose = codeMat 72
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 213) (codeMat 8) = codeMat 32 := by
      unfold actionA; rw [step113_415s70_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 470 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 24 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 24 (by decide)
    have hact : actionA (codeMat 273) (codeMat 213) (codeMat 24) = codeMat 24 := by
      unfold actionA; rw [step113_415s70_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 24 * (codeMat 470 : Mat3).transpose = codeMat 24
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 213) (codeMat 1) = codeMat 4 := by
      unfold actionA; rw [step113_415s70_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 470 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 6 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 6 (by decide)
    have hact : actionA (codeMat 273) (codeMat 213) (codeMat 6) = codeMat 2 := by
      unfold actionA; rw [step113_415s70_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 6 * (codeMat 470 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 5 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 5 (by decide)
    have hact : actionA (codeMat 273) (codeMat 213) (codeMat 5) = codeMat 1 := by
      unfold actionA; rw [step113_415s70_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 5 * (codeMat 470 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row70_qr : QuotientRankAtLeast step113_415ActualSource70 9 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 213 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 213) flatW_7) 9 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 213) hP hQ flatW_7 9 QiushiMatmul.flatSeed_7
  exact quotientRankAtLeast_mono step113_415s70_source_le hAct

-- Source 71: row 1972, orbit 7, lb 9, cap 7
def step113_415ActualSource71 : Submodule F2 Mat3 := spanCodes [264, 64, 32, 24, 4, 2, 1]

theorem step113_415_row71_W_le_source : o415W ≤ step113_415ActualSource71 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource71
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [264, 64, 32, 24, 4, 2, 1] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [264, 64, 32, 24, 4, 2, 1] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [264, 64, 32, 24, 4, 2, 1] 2 (by decide)

private theorem step113_415s71_QtInv :
    (codeMat 212 : Mat3).transpose⁻¹ = (codeMat 86 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 212 : Mat3).transpose * (codeMat 86 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s71_source_le :
    step113_415ActualSource71 ≤ actionW (codeMat 273) (codeMat 212) flatW_7 := by
  apply step113_415_spanCodes_le_of_gens [264, 64, 32, 24, 4, 2, 1]
    (actionW (codeMat 273) (codeMat 212) flatW_7)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 96 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 96 (by decide)
    have hact : actionA (codeMat 273) (codeMat 212) (codeMat 96) = codeMat 264 := by
      unfold actionA; rw [step113_415s71_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 96 * (codeMat 86 : Mat3).transpose = codeMat 264
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 256 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 273) (codeMat 212) (codeMat 256) = codeMat 64 := by
      unfold actionA; rw [step113_415s71_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 256 * (codeMat 86 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 212) (codeMat 8) = codeMat 32 := by
      unfold actionA; rw [step113_415s71_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 86 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 16 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 16 (by decide)
    have hact : actionA (codeMat 273) (codeMat 212) (codeMat 16) = codeMat 24 := by
      unfold actionA; rw [step113_415s71_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 16 * (codeMat 86 : Mat3).transpose = codeMat 24
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 212) (codeMat 1) = codeMat 4 := by
      unfold actionA; rw [step113_415s71_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 86 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 6 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 6 (by decide)
    have hact : actionA (codeMat 273) (codeMat 212) (codeMat 6) = codeMat 2 := by
      unfold actionA; rw [step113_415s71_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 6 * (codeMat 86 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 4 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 4 (by decide)
    have hact : actionA (codeMat 273) (codeMat 212) (codeMat 4) = codeMat 1 := by
      unfold actionA; rw [step113_415s71_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 4 * (codeMat 86 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row71_qr : QuotientRankAtLeast step113_415ActualSource71 9 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 212 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 212) flatW_7) 9 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 212) hP hQ flatW_7 9 QiushiMatmul.flatSeed_7
  exact quotientRankAtLeast_mono step113_415s71_source_le hAct

-- Source 72: row 2081, orbit 7, lb 9, cap 7
def step113_415ActualSource72 : Submodule F2 Mat3 := spanCodes [272, 128, 64, 56, 4, 2, 1]

theorem step113_415_row72_W_le_source : o415W ≤ step113_415ActualSource72 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource72
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 128, 64, 56, 4, 2, 1] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 128, 64, 56, 4, 2, 1] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 128, 64, 56, 4, 2, 1] 2 (by decide)

private theorem step113_415s72_QtInv :
    (codeMat 299 : Mat3).transpose⁻¹ = (codeMat 318 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 299 : Mat3).transpose * (codeMat 318 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s72_source_le :
    step113_415ActualSource72 ≤ actionW (codeMat 161) (codeMat 299) flatW_7 := by
  apply step113_415_spanCodes_le_of_gens [272, 128, 64, 56, 4, 2, 1]
    (actionW (codeMat 161) (codeMat 299) flatW_7)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 112 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 112 (by decide)
    have hact : actionA (codeMat 161) (codeMat 299) (codeMat 112) = codeMat 272 := by
      unfold actionA; rw [step113_415s72_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 112 * (codeMat 318 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 8 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 161) (codeMat 299) (codeMat 8) = codeMat 128 := by
      unfold actionA; rw [step113_415s72_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 8 * (codeMat 318 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 24 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 24 (by decide)
    have hact : actionA (codeMat 161) (codeMat 299) (codeMat 24) = codeMat 64 := by
      unfold actionA; rw [step113_415s72_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 24 * (codeMat 318 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 161) (codeMat 299) (codeMat 256) = codeMat 56 := by
      unfold actionA; rw [step113_415s72_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 256 * (codeMat 318 : Mat3).transpose = codeMat 56
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 6 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 6 (by decide)
    have hact : actionA (codeMat 161) (codeMat 299) (codeMat 6) = codeMat 4 := by
      unfold actionA; rw [step113_415s72_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 6 * (codeMat 318 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 299) (codeMat 1) = codeMat 2 := by
      unfold actionA; rw [step113_415s72_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 318 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 3 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 161) (codeMat 299) (codeMat 3) = codeMat 1 := by
      unfold actionA; rw [step113_415s72_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 3 * (codeMat 318 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row72_qr : QuotientRankAtLeast step113_415ActualSource72 9 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 299 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 299) flatW_7) 9 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 299) hP hQ flatW_7 9 QiushiMatmul.flatSeed_7
  exact quotientRankAtLeast_mono step113_415s72_source_le hAct

-- Source 73: row 2175, orbit 10, lb 12, cap 4
def step113_415ActualSource73 : Submodule F2 Mat3 := spanCodes [257, 137, 72, 32, 16, 4, 2]

theorem step113_415_row73_W_le_source : o415W ≤ step113_415ActualSource73 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource73
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [257, 137, 72, 32, 16, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [257, 137, 72, 32, 16, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [257, 137, 72, 32, 16, 4, 2] 2 (by decide)

private theorem step113_415s73_QtInv :
    (codeMat 115 : Mat3).transpose⁻¹ = (codeMat 492 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 115 : Mat3).transpose * (codeMat 492 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s73_source_le :
    step113_415ActualSource73 ≤ actionW (codeMat 266) (codeMat 115) orbit10W := by
  apply step113_415_spanCodes_le_of_gens [257, 137, 72, 32, 16, 4, 2]
    (actionW (codeMat 266) (codeMat 115) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 168 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 168 (by decide)
    have hact : actionA (codeMat 266) (codeMat 115) (codeMat 168) = codeMat 257 := by
      unfold actionA; rw [step113_415s73_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 168 * (codeMat 492 : Mat3).transpose = codeMat 257
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 237 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 237 (by decide)
    have hact : actionA (codeMat 266) (codeMat 115) (codeMat 237) = codeMat 137 := by
      unfold actionA; rw [step113_415s73_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 237 * (codeMat 492 : Mat3).transpose = codeMat 137
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 325 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 325 (by decide)
    have hact : actionA (codeMat 266) (codeMat 115) (codeMat 325) = codeMat 72 := by
      unfold actionA; rw [step113_415s73_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 325 * (codeMat 492 : Mat3).transpose = codeMat 72
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 115) (codeMat 2) = codeMat 32 := by
      unfold actionA; rw [step113_415s73_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 492 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 3 (by decide)
    have hact : actionA (codeMat 266) (codeMat 115) (codeMat 3) = codeMat 16 := by
      unfold actionA; rw [step113_415s73_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 3 * (codeMat 492 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 115) (codeMat 16) = codeMat 4 := by
      unfold actionA; rw [step113_415s73_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 492 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 24 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide)
    have hact : actionA (codeMat 266) (codeMat 115) (codeMat 24) = codeMat 2 := by
      unfold actionA; rw [step113_415s73_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 24 * (codeMat 492 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row73_qr : QuotientRankAtLeast step113_415ActualSource73 12 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 115 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 115) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 115) hP hQ orbit10W 12 QiushiMatmul.orbit10_lb12
  exact quotientRankAtLeast_mono step113_415s73_source_le hAct

-- Source 74: row 2181, orbit 10, lb 12, cap 4
def step113_415ActualSource74 : Submodule F2 Mat3 := spanCodes [256, 128, 97, 17, 8, 4, 2]

theorem step113_415_row74_W_le_source : o415W ≤ step113_415ActualSource74 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource74
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 97, 17, 8, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 97, 17, 8, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 97, 17, 8, 4, 2] 2 (by decide)

private theorem step113_415s74_QtInv :
    (codeMat 116 : Mat3).transpose⁻¹ = (codeMat 92 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 116 : Mat3).transpose * (codeMat 92 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s74_source_le :
    step113_415ActualSource74 ≤ actionW (codeMat 140) (codeMat 116) orbit10W := by
  apply step113_415_spanCodes_le_of_gens [256, 128, 97, 17, 8, 4, 2]
    (actionW (codeMat 140) (codeMat 116) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 3 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 3 (by decide)
    have hact : actionA (codeMat 140) (codeMat 116) (codeMat 3) = codeMat 256 := by
      unfold actionA; rw [step113_415s74_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 3 * (codeMat 92 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 140) (codeMat 116) (codeMat 2) = codeMat 128 := by
      unfold actionA; rw [step113_415s74_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 2 * (codeMat 92 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 228 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 228 (by decide)
    have hact : actionA (codeMat 140) (codeMat 116) (codeMat 228) = codeMat 97 := by
      unfold actionA; rw [step113_415s74_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 228 * (codeMat 92 : Mat3).transpose = codeMat 97
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 140) (codeMat 116) (codeMat 160) = codeMat 17 := by
      unfold actionA; rw [step113_415s74_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 160 * (codeMat 92 : Mat3).transpose = codeMat 17
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 140) (codeMat 116) (codeMat 256) = codeMat 8 := by
      unfold actionA; rw [step113_415s74_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 256 * (codeMat 92 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 24 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide)
    have hact : actionA (codeMat 140) (codeMat 116) (codeMat 24) = codeMat 4 := by
      unfold actionA; rw [step113_415s74_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 24 * (codeMat 92 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 140) (codeMat 116) (codeMat 16) = codeMat 2 := by
      unfold actionA; rw [step113_415s74_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 16 * (codeMat 92 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row74_qr : QuotientRankAtLeast step113_415ActualSource74 12 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 116 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 116) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 116) hP hQ orbit10W 12 QiushiMatmul.orbit10_lb12
  exact quotientRankAtLeast_mono step113_415s74_source_le hAct

-- Source 75: row 2253, orbit 14, lb 12, cap 4
def step113_415ActualSource75 : Submodule F2 Mat3 := spanCodes [256, 160, 97, 17, 8, 4, 2]

theorem step113_415_row75_W_le_source : o415W ≤ step113_415ActualSource75 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource75
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 97, 17, 8, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 97, 17, 8, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 97, 17, 8, 4, 2] 2 (by decide)

private theorem step113_415s75_QtInv :
    (codeMat 225 : Mat3).transpose⁻¹ = (codeMat 169 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 225 : Mat3).transpose * (codeMat 169 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s75_source_le :
    step113_415ActualSource75 ≤ actionW (codeMat 93) (codeMat 225) orbit14W := by
  apply step113_415_spanCodes_le_of_gens [256, 160, 97, 17, 8, 4, 2]
    (actionW (codeMat 93) (codeMat 225) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 130 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 130 (by decide)
    have hact : actionA (codeMat 93) (codeMat 225) (codeMat 130) = codeMat 256 := by
      unfold actionA; rw [step113_415s75_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 130 * (codeMat 169 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 404 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 404 (by decide)
    have hact : actionA (codeMat 93) (codeMat 225) (codeMat 404) = codeMat 160 := by
      unfold actionA; rw [step113_415s75_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 404 * (codeMat 169 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 149 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 149 (by decide)
    have hact : actionA (codeMat 93) (codeMat 225) (codeMat 149) = codeMat 97 := by
      unfold actionA; rw [step113_415s75_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 149 * (codeMat 169 : Mat3).transpose = codeMat 97
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 93) (codeMat 225) (codeMat 96) = codeMat 17 := by
      unfold actionA; rw [step113_415s75_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 96 * (codeMat 169 : Mat3).transpose = codeMat 17
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 93) (codeMat 225) (codeMat 360) = codeMat 8 := by
      unfold actionA; rw [step113_415s75_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 360 * (codeMat 169 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 93) (codeMat 225) (codeMat 128) = codeMat 4 := by
      unfold actionA; rw [step113_415s75_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 128 * (codeMat 169 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 93) (codeMat 225) (codeMat 256) = codeMat 2 := by
      unfold actionA; rw [step113_415s75_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 256 * (codeMat 169 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row75_qr : QuotientRankAtLeast step113_415ActualSource75 12 := by
  have hP : Invertible (codeMat 93 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 93) (codeMat 225) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 93) (codeMat 225) hP hQ orbit14W 12 QiushiMatmul.orbit14_lb12
  exact quotientRankAtLeast_mono step113_415s75_source_le hAct

-- Source 76: row 2254, orbit 14, lb 12, cap 4
def step113_415ActualSource76 : Submodule F2 Mat3 := spanCodes [257, 160, 97, 16, 9, 4, 2]

theorem step113_415_row76_W_le_source : o415W ≤ step113_415ActualSource76 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource76
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [257, 160, 97, 16, 9, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [257, 160, 97, 16, 9, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [257, 160, 97, 16, 9, 4, 2] 2 (by decide)

private theorem step113_415s76_QtInv :
    (codeMat 281 : Mat3).transpose⁻¹ = (codeMat 281 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 281 : Mat3).transpose * (codeMat 281 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s76_source_le :
    step113_415ActualSource76 ≤ actionW (codeMat 107) (codeMat 281) orbit14W := by
  apply step113_415_spanCodes_le_of_gens [257, 160, 97, 16, 9, 4, 2]
    (actionW (codeMat 107) (codeMat 281) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 480 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 480 (by decide)
    have hact : actionA (codeMat 107) (codeMat 281) (codeMat 480) = codeMat 257 := by
      unfold actionA; rw [step113_415s76_QtInv]
      show (codeMat 107 : Mat3).transpose * codeMat 480 * (codeMat 281 : Mat3).transpose = codeMat 257
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 404 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 404 (by decide)
    have hact : actionA (codeMat 107) (codeMat 281) (codeMat 404) = codeMat 160 := by
      unfold actionA; rw [step113_415s76_QtInv]
      show (codeMat 107 : Mat3).transpose * codeMat 404 * (codeMat 281 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 284 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 284 (by decide)
    have hact : actionA (codeMat 107) (codeMat 281) (codeMat 284) = codeMat 97 := by
      unfold actionA; rw [step113_415s76_QtInv]
      show (codeMat 107 : Mat3).transpose * codeMat 284 * (codeMat 281 : Mat3).transpose = codeMat 97
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 130 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 130 (by decide)
    have hact : actionA (codeMat 107) (codeMat 281) (codeMat 130) = codeMat 16 := by
      unfold actionA; rw [step113_415s76_QtInv]
      show (codeMat 107 : Mat3).transpose * codeMat 130 * (codeMat 281 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 107) (codeMat 281) (codeMat 3) = codeMat 9 := by
      unfold actionA; rw [step113_415s76_QtInv]
      show (codeMat 107 : Mat3).transpose * codeMat 3 * (codeMat 281 : Mat3).transpose = codeMat 9
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 107) (codeMat 281) (codeMat 256) = codeMat 4 := by
      unfold actionA; rw [step113_415s76_QtInv]
      show (codeMat 107 : Mat3).transpose * codeMat 256 * (codeMat 281 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 107) (codeMat 281) (codeMat 128) = codeMat 2 := by
      unfold actionA; rw [step113_415s76_QtInv]
      show (codeMat 107 : Mat3).transpose * codeMat 128 * (codeMat 281 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row76_qr : QuotientRankAtLeast step113_415ActualSource76 12 := by
  have hP : Invertible (codeMat 107 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 281 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 107) (codeMat 281) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 107) (codeMat 281) hP hQ orbit14W 12 QiushiMatmul.orbit14_lb12
  exact quotientRankAtLeast_mono step113_415s76_source_le hAct

-- Source 77: row 28, orbit 101, lb 15, cap 1
def step113_415ActualSource77 : Submodule F2 Mat3 := spanCodes [273, 32, 8, 4, 2]

theorem step113_415_row77_W_le_source : o415W ≤ step113_415ActualSource77 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource77
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 32, 8, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 32, 8, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 32, 8, 4, 2] 2 (by decide)

private theorem step113_415s77_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s77_source_le :
    step113_415ActualSource77 ≤ actionW (codeMat 266) (codeMat 140) orbit101W := by
  apply step113_415_spanCodes_le_of_gens [273, 32, 8, 4, 2]
    (actionW (codeMat 266) (codeMat 140) orbit101W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 84 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 84 (by decide)
    have hact : actionA (codeMat 266) (codeMat 140) (codeMat 84) = codeMat 273 := by
      unfold actionA; rw [step113_415s77_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 84 * (codeMat 98 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 140) (codeMat 1) = codeMat 32 := by
      unfold actionA; rw [step113_415s77_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 140) (codeMat 2) = codeMat 8 := by
      unfold actionA; rw [step113_415s77_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 98 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 140) (codeMat 8) = codeMat 4 := by
      unfold actionA; rw [step113_415s77_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 32 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 32 (by decide)
    have hact : actionA (codeMat 266) (codeMat 140) (codeMat 32) = codeMat 2 := by
      unfold actionA; rw [step113_415s77_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 98 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row77_qr : QuotientRankAtLeast step113_415ActualSource77 15 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 140) orbit101W) 15 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 140) hP hQ orbit101W 15 QiushiMatmul.orbit101_lb15
  exact quotientRankAtLeast_mono step113_415s77_source_le hAct

-- Source 78: row 41, orbit 101, lb 15, cap 1
def step113_415ActualSource78 : Submodule F2 Mat3 := spanCodes [273, 128, 64, 4, 2]

theorem step113_415_row78_W_le_source : o415W ≤ step113_415ActualSource78 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource78
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 128, 64, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 128, 64, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 128, 64, 4, 2] 2 (by decide)

private theorem step113_415s78_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s78_source_le :
    step113_415ActualSource78 ≤ actionW (codeMat 140) (codeMat 266) orbit101W := by
  apply step113_415_spanCodes_le_of_gens [273, 128, 64, 4, 2]
    (actionW (codeMat 140) (codeMat 266) orbit101W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 84 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 84 (by decide)
    have hact : actionA (codeMat 140) (codeMat 266) (codeMat 84) = codeMat 273 := by
      unfold actionA; rw [step113_415s78_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 84 * (codeMat 266 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 1 (by decide)
    have hact : actionA (codeMat 140) (codeMat 266) (codeMat 1) = codeMat 128 := by
      unfold actionA; rw [step113_415s78_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 2 (by decide)
    have hact : actionA (codeMat 140) (codeMat 266) (codeMat 2) = codeMat 64 := by
      unfold actionA; rw [step113_415s78_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 2 * (codeMat 266 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 32 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 32 (by decide)
    have hact : actionA (codeMat 140) (codeMat 266) (codeMat 32) = codeMat 4 := by
      unfold actionA; rw [step113_415s78_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 32 * (codeMat 266 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 8 (by decide)
    have hact : actionA (codeMat 140) (codeMat 266) (codeMat 8) = codeMat 2 := by
      unfold actionA; rw [step113_415s78_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 8 * (codeMat 266 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row78_qr : QuotientRankAtLeast step113_415ActualSource78 15 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 266) orbit101W) 15 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 266) hP hQ orbit101W 15 QiushiMatmul.orbit101_lb15
  exact quotientRankAtLeast_mono step113_415s78_source_le hAct

-- Source 79: row 43, orbit 101, lb 15, cap 1
def step113_415ActualSource79 : Submodule F2 Mat3 := spanCodes [273, 128, 80, 4, 2]

theorem step113_415_row79_W_le_source : o415W ≤ step113_415ActualSource79 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource79
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 128, 80, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 128, 80, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 128, 80, 4, 2] 2 (by decide)

private theorem step113_415s79_QtInv :
    (codeMat 330 : Mat3).transpose⁻¹ = (codeMat 394 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 330 : Mat3).transpose * (codeMat 394 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s79_source_le :
    step113_415ActualSource79 ≤ actionW (codeMat 141) (codeMat 330) orbit101W := by
  apply step113_415_spanCodes_le_of_gens [273, 128, 80, 4, 2]
    (actionW (codeMat 141) (codeMat 330) orbit101W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 84 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 84 (by decide)
    have hact : actionA (codeMat 141) (codeMat 330) (codeMat 84) = codeMat 273 := by
      unfold actionA; rw [step113_415s79_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 84 * (codeMat 394 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 9 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 9 (by decide)
    have hact : actionA (codeMat 141) (codeMat 330) (codeMat 9) = codeMat 128 := by
      unfold actionA; rw [step113_415s79_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 9 * (codeMat 394 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 118 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 118 (by decide)
    have hact : actionA (codeMat 141) (codeMat 330) (codeMat 118) = codeMat 80 := by
      unfold actionA; rw [step113_415s79_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 118 * (codeMat 394 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 32 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 32 (by decide)
    have hact : actionA (codeMat 141) (codeMat 330) (codeMat 32) = codeMat 4 := by
      unfold actionA; rw [step113_415s79_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 32 * (codeMat 394 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 8 (by decide)
    have hact : actionA (codeMat 141) (codeMat 330) (codeMat 8) = codeMat 2 := by
      unfold actionA; rw [step113_415s79_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 8 * (codeMat 394 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row79_qr : QuotientRankAtLeast step113_415ActualSource79 15 := by
  have hP : Invertible (codeMat 141 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 330 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 141) (codeMat 330) orbit101W) 15 :=
    @quotientRankAtLeast_action (codeMat 141) (codeMat 330) hP hQ orbit101W 15 QiushiMatmul.orbit101_lb15
  exact quotientRankAtLeast_mono step113_415s79_source_le hAct

-- Source 80: row 63, orbit 103, lb 15, cap 1
def step113_415ActualSource80 : Submodule F2 Mat3 := spanCodes [273, 145, 65, 4, 2]

theorem step113_415_row80_W_le_source : o415W ≤ step113_415ActualSource80 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource80
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 145, 65, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 145, 65, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 145, 65, 4, 2] 2 (by decide)

private theorem step113_415s80_QtInv :
    (codeMat 116 : Mat3).transpose⁻¹ = (codeMat 92 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 116 : Mat3).transpose * (codeMat 92 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s80_source_le :
    step113_415ActualSource80 ≤ actionW (codeMat 425) (codeMat 116) o103W_mono := by
  apply step113_415_spanCodes_le_of_gens [273, 145, 65, 4, 2]
    (actionW (codeMat 425) (codeMat 116) o103W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 141 ∈ o103W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 8, 2, 1] 141 (by decide)
    have hact : actionA (codeMat 425) (codeMat 116) (codeMat 141) = codeMat 273 := by
      unfold actionA; rw [step113_415s80_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 141 * (codeMat 92 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 132 ∈ o103W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 8, 2, 1] 132 (by decide)
    have hact : actionA (codeMat 425) (codeMat 116) (codeMat 132) = codeMat 145 := by
      unfold actionA; rw [step113_415s80_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 132 * (codeMat 92 : Mat3).transpose = codeMat 145
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 32 ∈ o103W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 425) (codeMat 116) (codeMat 32) = codeMat 65 := by
      unfold actionA; rw [step113_415s80_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 32 * (codeMat 92 : Mat3).transpose = codeMat 65
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 3 ∈ o103W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 8, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 425) (codeMat 116) (codeMat 3) = codeMat 4 := by
      unfold actionA; rw [step113_415s80_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 3 * (codeMat 92 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o103W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 425) (codeMat 116) (codeMat 2) = codeMat 2 := by
      unfold actionA; rw [step113_415s80_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 2 * (codeMat 92 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row80_qr : QuotientRankAtLeast step113_415ActualSource80 15 := by
  have hP : Invertible (codeMat 425 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 116 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 425) (codeMat 116) o103W_mono) 15 :=
    @quotientRankAtLeast_action (codeMat 425) (codeMat 116) hP hQ o103W_mono 15 QiushiMatmul.orbit103_lb15_mono
  exact quotientRankAtLeast_mono step113_415s80_source_le hAct

-- Source 81: row 64, orbit 103, lb 15, cap 1
def step113_415ActualSource81 : Submodule F2 Mat3 := spanCodes [256, 193, 17, 4, 2]

theorem step113_415_row81_W_le_source : o415W ≤ step113_415ActualSource81 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource81
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 193, 17, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 193, 17, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 193, 17, 4, 2] 2 (by decide)

private theorem step113_415s81_QtInv :
    (codeMat 92 : Mat3).transpose⁻¹ = (codeMat 116 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 92 : Mat3).transpose * (codeMat 116 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s81_source_le :
    step113_415ActualSource81 ≤ actionW (codeMat 169) (codeMat 92) o103W_mono := by
  apply step113_415_spanCodes_le_of_gens [256, 193, 17, 4, 2]
    (actionW (codeMat 169) (codeMat 92) o103W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 9 ∈ o103W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 8, 2, 1] 9 (by decide)
    have hact : actionA (codeMat 169) (codeMat 92) (codeMat 9) = codeMat 256 := by
      unfold actionA; rw [step113_415s81_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 9 * (codeMat 116 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 34 ∈ o103W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 8, 2, 1] 34 (by decide)
    have hact : actionA (codeMat 169) (codeMat 92) (codeMat 34) = codeMat 193 := by
      unfold actionA; rw [step113_415s81_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 34 * (codeMat 116 : Mat3).transpose = codeMat 193
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 134 ∈ o103W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 8, 2, 1] 134 (by decide)
    have hact : actionA (codeMat 169) (codeMat 92) (codeMat 134) = codeMat 17 := by
      unfold actionA; rw [step113_415s81_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 134 * (codeMat 116 : Mat3).transpose = codeMat 17
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o103W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 92) (codeMat 1) = codeMat 4 := by
      unfold actionA; rw [step113_415s81_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * (codeMat 116 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o103W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 169) (codeMat 92) (codeMat 2) = codeMat 2 := by
      unfold actionA; rw [step113_415s81_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 2 * (codeMat 116 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row81_qr : QuotientRankAtLeast step113_415ActualSource81 15 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 92 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 92) o103W_mono) 15 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 92) hP hQ o103W_mono 15 QiushiMatmul.orbit103_lb15_mono
  exact quotientRankAtLeast_mono step113_415s81_source_le hAct

-- Source 82: row 298, orbit 141, lb 15, cap 1
def step113_415ActualSource82 : Submodule F2 Mat3 := spanCodes [273, 184, 104, 4, 2]

theorem step113_415_row82_W_le_source : o415W ≤ step113_415ActualSource82 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource82
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 184, 104, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 184, 104, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 184, 104, 4, 2] 2 (by decide)

private theorem step113_415s82_QtInv :
    (codeMat 107 : Mat3).transpose⁻¹ = (codeMat 428 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 107 : Mat3).transpose * (codeMat 428 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s82_source_le :
    step113_415ActualSource82 ≤ actionW (codeMat 169) (codeMat 107) o141W_wc := by
  apply step113_415_spanCodes_le_of_gens [273, 184, 104, 4, 2]
    (actionW (codeMat 169) (codeMat 107) o141W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 85 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 85 (by decide)
    have hact : actionA (codeMat 169) (codeMat 107) (codeMat 85) = codeMat 273 := by
      unfold actionA; rw [step113_415s82_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 85 * (codeMat 428 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 265 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 265 (by decide)
    have hact : actionA (codeMat 169) (codeMat 107) (codeMat 265) = codeMat 184 := by
      unfold actionA; rw [step113_415s82_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 265 * (codeMat 428 : Mat3).transpose = codeMat 184
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 383 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 383 (by decide)
    have hact : actionA (codeMat 169) (codeMat 107) (codeMat 383) = codeMat 104 := by
      unfold actionA; rw [step113_415s82_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 383 * (codeMat 428 : Mat3).transpose = codeMat 104
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 169) (codeMat 107) (codeMat 2) = codeMat 4 := by
      unfold actionA; rw [step113_415s82_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 2 * (codeMat 428 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 107) (codeMat 1) = codeMat 2 := by
      unfold actionA; rw [step113_415s82_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * (codeMat 428 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row82_qr : QuotientRankAtLeast step113_415ActualSource82 15 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 107 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 107) o141W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 107) hP hQ o141W_wc 15 QiushiMatmul.step109_orbit141_lb15_wc
  exact quotientRankAtLeast_mono step113_415s82_source_le hAct

-- Source 83: row 299, orbit 141, lb 15, cap 1
def step113_415ActualSource83 : Submodule F2 Mat3 := spanCodes [273, 185, 105, 4, 2]

theorem step113_415_row83_W_le_source : o415W ≤ step113_415ActualSource83 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource83
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 185, 105, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 185, 105, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 185, 105, 4, 2] 2 (by decide)

private theorem step113_415s83_QtInv :
    (codeMat 107 : Mat3).transpose⁻¹ = (codeMat 428 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 107 : Mat3).transpose * (codeMat 428 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s83_source_le :
    step113_415ActualSource83 ≤ actionW (codeMat 233) (codeMat 107) o141W_wc := by
  apply step113_415_spanCodes_le_of_gens [273, 185, 105, 4, 2]
    (actionW (codeMat 233) (codeMat 107) o141W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 84 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 84 (by decide)
    have hact : actionA (codeMat 233) (codeMat 107) (codeMat 84) = codeMat 273 := by
      unfold actionA; rw [step113_415s83_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 84 * (codeMat 428 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 266 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 266 (by decide)
    have hact : actionA (codeMat 233) (codeMat 107) (codeMat 266) = codeMat 185 := by
      unfold actionA; rw [step113_415s83_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 266 * (codeMat 428 : Mat3).transpose = codeMat 185
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 381 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 381 (by decide)
    have hact : actionA (codeMat 233) (codeMat 107) (codeMat 381) = codeMat 105 := by
      unfold actionA; rw [step113_415s83_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 381 * (codeMat 428 : Mat3).transpose = codeMat 105
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 233) (codeMat 107) (codeMat 2) = codeMat 4 := by
      unfold actionA; rw [step113_415s83_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 2 * (codeMat 428 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o141W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [264, 84, 32, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 233) (codeMat 107) (codeMat 1) = codeMat 2 := by
      unfold actionA; rw [step113_415s83_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 1 * (codeMat 428 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row83_qr : QuotientRankAtLeast step113_415ActualSource83 15 := by
  have hP : Invertible (codeMat 233 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 107 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 233) (codeMat 107) o141W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 233) (codeMat 107) hP hQ o141W_wc 15 QiushiMatmul.step109_orbit141_lb15_wc
  exact quotientRankAtLeast_mono step113_415s83_source_le hAct

-- Source 84: row 458, orbit 144, lb 15, cap 1
def step113_415ActualSource84 : Submodule F2 Mat3 := spanCodes [273, 136, 88, 4, 2]

theorem step113_415_row84_W_le_source : o415W ≤ step113_415ActualSource84 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource84
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 136, 88, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 136, 88, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 136, 88, 4, 2] 2 (by decide)

private theorem step113_415s84_QtInv :
    (codeMat 107 : Mat3).transpose⁻¹ = (codeMat 428 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 107 : Mat3).transpose * (codeMat 428 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s84_source_le :
    step113_415ActualSource84 ≤ actionW (codeMat 233) (codeMat 107) o144W := by
  apply step113_415_spanCodes_le_of_gens [273, 136, 88, 4, 2]
    (actionW (codeMat 233) (codeMat 107) o144W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 84 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 84 (by decide)
    have hact : actionA (codeMat 233) (codeMat 107) (codeMat 84) = codeMat 273 := by
      unfold actionA; rw [step113_415s84_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 84 * (codeMat 428 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 462 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 462 (by decide)
    have hact : actionA (codeMat 233) (codeMat 107) (codeMat 462) = codeMat 136 := by
      unfold actionA; rw [step113_415s84_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 462 * (codeMat 428 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 441 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 441 (by decide)
    have hact : actionA (codeMat 233) (codeMat 107) (codeMat 441) = codeMat 88 := by
      unfold actionA; rw [step113_415s84_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 441 * (codeMat 428 : Mat3).transpose = codeMat 88
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 233) (codeMat 107) (codeMat 2) = codeMat 4 := by
      unfold actionA; rw [step113_415s84_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 2 * (codeMat 428 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 233) (codeMat 107) (codeMat 1) = codeMat 2 := by
      unfold actionA; rw [step113_415s84_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 1 * (codeMat 428 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row84_qr : QuotientRankAtLeast step113_415ActualSource84 15 := by
  have hP : Invertible (codeMat 233 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 107 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 233) (codeMat 107) o144W) 15 :=
    @quotientRankAtLeast_action (codeMat 233) (codeMat 107) hP hQ o144W 15 QiushiMatmul.step99_orbit144_lb15_unconditional
  exact quotientRankAtLeast_mono step113_415s84_source_le hAct

-- Source 85: row 459, orbit 144, lb 15, cap 1
def step113_415ActualSource85 : Submodule F2 Mat3 := spanCodes [273, 137, 89, 4, 2]

theorem step113_415_row85_W_le_source : o415W ≤ step113_415ActualSource85 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource85
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 137, 89, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 137, 89, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 137, 89, 4, 2] 2 (by decide)

private theorem step113_415s85_QtInv :
    (codeMat 107 : Mat3).transpose⁻¹ = (codeMat 428 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 107 : Mat3).transpose * (codeMat 428 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s85_source_le :
    step113_415ActualSource85 ≤ actionW (codeMat 169) (codeMat 107) o144W := by
  apply step113_415_spanCodes_le_of_gens [273, 137, 89, 4, 2]
    (actionW (codeMat 169) (codeMat 107) o144W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 85 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 85 (by decide)
    have hact : actionA (codeMat 169) (codeMat 107) (codeMat 85) = codeMat 273 := by
      unfold actionA; rw [step113_415s85_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 85 * (codeMat 428 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 462 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 462 (by decide)
    have hact : actionA (codeMat 169) (codeMat 107) (codeMat 462) = codeMat 137 := by
      unfold actionA; rw [step113_415s85_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 462 * (codeMat 428 : Mat3).transpose = codeMat 137
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 440 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 440 (by decide)
    have hact : actionA (codeMat 169) (codeMat 107) (codeMat 440) = codeMat 89 := by
      unfold actionA; rw [step113_415s85_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 440 * (codeMat 428 : Mat3).transpose = codeMat 89
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 169) (codeMat 107) (codeMat 2) = codeMat 4 := by
      unfold actionA; rw [step113_415s85_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 2 * (codeMat 428 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 107) (codeMat 1) = codeMat 2 := by
      unfold actionA; rw [step113_415s85_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * (codeMat 428 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row85_qr : QuotientRankAtLeast step113_415ActualSource85 15 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 107 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 107) o144W) 15 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 107) hP hQ o144W 15 QiushiMatmul.step99_orbit144_lb15_unconditional
  exact quotientRankAtLeast_mono step113_415s85_source_le hAct

-- Source 86: row 463, orbit 144, lb 15, cap 1
def step113_415ActualSource86 : Submodule F2 Mat3 := spanCodes [273, 169, 113, 4, 2]

theorem step113_415_row86_W_le_source : o415W ≤ step113_415ActualSource86 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource86
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 169, 113, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 169, 113, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 169, 113, 4, 2] 2 (by decide)

private theorem step113_415s86_QtInv :
    (codeMat 123 : Mat3).transpose⁻¹ = (codeMat 236 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 123 : Mat3).transpose * (codeMat 236 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s86_source_le :
    step113_415ActualSource86 ≤ actionW (codeMat 241) (codeMat 123) o144W := by
  apply step113_415_spanCodes_le_of_gens [273, 169, 113, 4, 2]
    (actionW (codeMat 241) (codeMat 123) o144W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 86 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 86 (by decide)
    have hact : actionA (codeMat 241) (codeMat 123) (codeMat 86) = codeMat 273 := by
      unfold actionA; rw [step113_415s86_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 86 * (codeMat 236 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 409 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 409 (by decide)
    have hact : actionA (codeMat 241) (codeMat 123) (codeMat 409) = codeMat 169 := by
      unfold actionA; rw [step113_415s86_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 409 * (codeMat 236 : Mat3).transpose = codeMat 169
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 441 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 441 (by decide)
    have hact : actionA (codeMat 241) (codeMat 123) (codeMat 441) = codeMat 113 := by
      unfold actionA; rw [step113_415s86_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 441 * (codeMat 236 : Mat3).transpose = codeMat 113
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 241) (codeMat 123) (codeMat 2) = codeMat 4 := by
      unfold actionA; rw [step113_415s86_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 2 * (codeMat 236 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 241) (codeMat 123) (codeMat 3) = codeMat 2 := by
      unfold actionA; rw [step113_415s86_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 3 * (codeMat 236 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row86_qr : QuotientRankAtLeast step113_415ActualSource86 15 := by
  have hP : Invertible (codeMat 241 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 123 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 241) (codeMat 123) o144W) 15 :=
    @quotientRankAtLeast_action (codeMat 241) (codeMat 123) hP hQ o144W 15 QiushiMatmul.step99_orbit144_lb15_unconditional
  exact quotientRankAtLeast_mono step113_415s86_source_le hAct

-- Source 87: row 464, orbit 144, lb 15, cap 1
def step113_415ActualSource87 : Submodule F2 Mat3 := spanCodes [273, 168, 113, 4, 2]

theorem step113_415_row87_W_le_source : o415W ≤ step113_415ActualSource87 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource87
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 168, 113, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 168, 113, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 168, 113, 4, 2] 2 (by decide)

private theorem step113_415s87_QtInv :
    (codeMat 123 : Mat3).transpose⁻¹ = (codeMat 236 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 123 : Mat3).transpose * (codeMat 236 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s87_source_le :
    step113_415ActualSource87 ≤ actionW (codeMat 185) (codeMat 123) o144W := by
  apply step113_415_spanCodes_le_of_gens [273, 168, 113, 4, 2]
    (actionW (codeMat 185) (codeMat 123) o144W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 85 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 85 (by decide)
    have hact : actionA (codeMat 185) (codeMat 123) (codeMat 85) = codeMat 273 := by
      unfold actionA; rw [step113_415s87_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 85 * (codeMat 236 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 411 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 411 (by decide)
    have hact : actionA (codeMat 185) (codeMat 123) (codeMat 411) = codeMat 168 := by
      unfold actionA; rw [step113_415s87_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 411 * (codeMat 236 : Mat3).transpose = codeMat 168
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 440 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 440 (by decide)
    have hact : actionA (codeMat 185) (codeMat 123) (codeMat 440) = codeMat 113 := by
      unfold actionA; rw [step113_415s87_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 440 * (codeMat 236 : Mat3).transpose = codeMat 113
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 185) (codeMat 123) (codeMat 2) = codeMat 4 := by
      unfold actionA; rw [step113_415s87_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 2 * (codeMat 236 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 185) (codeMat 123) (codeMat 3) = codeMat 2 := by
      unfold actionA; rw [step113_415s87_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 3 * (codeMat 236 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row87_qr : QuotientRankAtLeast step113_415ActualSource87 15 := by
  have hP : Invertible (codeMat 185 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 123 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 185) (codeMat 123) o144W) 15 :=
    @quotientRankAtLeast_action (codeMat 185) (codeMat 123) hP hQ o144W 15 QiushiMatmul.step99_orbit144_lb15_unconditional
  exact quotientRankAtLeast_mono step113_415s87_source_le hAct

-- Source 88: row 484, orbit 144, lb 15, cap 1
def step113_415ActualSource88 : Submodule F2 Mat3 := spanCodes [273, 240, 8, 4, 2]

theorem step113_415_row88_W_le_source : o415W ≤ step113_415ActualSource88 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource88
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 240, 8, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 240, 8, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 240, 8, 4, 2] 2 (by decide)

private theorem step113_415s88_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s88_source_le :
    step113_415ActualSource88 ≤ actionW (codeMat 273) (codeMat 84) o144W := by
  apply step113_415_spanCodes_le_of_gens [273, 240, 8, 4, 2]
    (actionW (codeMat 273) (codeMat 84) o144W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 84 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 84 (by decide)
    have hact : actionA (codeMat 273) (codeMat 84) (codeMat 84) = codeMat 273 := by
      unfold actionA; rw [step113_415s88_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 84 * (codeMat 84 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 408 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 408 (by decide)
    have hact : actionA (codeMat 273) (codeMat 84) (codeMat 408) = codeMat 240 := by
      unfold actionA; rw [step113_415s88_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 408 * (codeMat 84 : Mat3).transpose = codeMat 240
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 32 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 273) (codeMat 84) (codeMat 32) = codeMat 8 := by
      unfold actionA; rw [step113_415s88_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 32 * (codeMat 84 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 84) (codeMat 1) = codeMat 4 := by
      unfold actionA; rw [step113_415s88_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 84 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 84) (codeMat 2) = codeMat 2 := by
      unfold actionA; rw [step113_415s88_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 84 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row88_qr : QuotientRankAtLeast step113_415ActualSource88 15 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 84) o144W) 15 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 84) hP hQ o144W 15 QiushiMatmul.step99_orbit144_lb15_unconditional
  exact quotientRankAtLeast_mono step113_415s88_source_le hAct

-- Source 89: row 488, orbit 144, lb 15, cap 1
def step113_415ActualSource89 : Submodule F2 Mat3 := spanCodes [273, 240, 9, 4, 2]

theorem step113_415_row89_W_le_source : o415W ≤ step113_415ActualSource89 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource89
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 240, 9, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 240, 9, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 240, 9, 4, 2] 2 (by decide)

private theorem step113_415s89_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s89_source_le :
    step113_415ActualSource89 ≤ actionW (codeMat 281) (codeMat 84) o144W := by
  apply step113_415_spanCodes_le_of_gens [273, 240, 9, 4, 2]
    (actionW (codeMat 281) (codeMat 84) o144W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 86 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 86 (by decide)
    have hact : actionA (codeMat 281) (codeMat 84) (codeMat 86) = codeMat 273 := by
      unfold actionA; rw [step113_415s89_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 86 * (codeMat 84 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 411 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 411 (by decide)
    have hact : actionA (codeMat 281) (codeMat 84) (codeMat 411) = codeMat 240 := by
      unfold actionA; rw [step113_415s89_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 411 * (codeMat 84 : Mat3).transpose = codeMat 240
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 32 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 281) (codeMat 84) (codeMat 32) = codeMat 9 := by
      unfold actionA; rw [step113_415s89_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 32 * (codeMat 84 : Mat3).transpose = codeMat 9
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 281) (codeMat 84) (codeMat 1) = codeMat 4 := by
      unfold actionA; rw [step113_415s89_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 1 * (codeMat 84 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 281) (codeMat 84) (codeMat 2) = codeMat 2 := by
      unfold actionA; rw [step113_415s89_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 2 * (codeMat 84 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row89_qr : QuotientRankAtLeast step113_415ActualSource89 15 := by
  have hP : Invertible (codeMat 281 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 281) (codeMat 84) o144W) 15 :=
    @quotientRankAtLeast_action (codeMat 281) (codeMat 84) hP hQ o144W 15 QiushiMatmul.step99_orbit144_lb15_unconditional
  exact quotientRankAtLeast_mono step113_415s89_source_le hAct

-- Source 90: row 729, orbit 29, lb 15, cap 1
def step113_415ActualSource90 : Submodule F2 Mat3 := spanCodes [273, 144, 89, 49, 4, 2]

theorem step113_415_row90_W_le_source : o415W ≤ step113_415ActualSource90 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource90
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 144, 89, 49, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 144, 89, 49, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 144, 89, 49, 4, 2] 2 (by decide)

private theorem step113_415s90_QtInv :
    (codeMat 86 : Mat3).transpose⁻¹ = (codeMat 212 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 86 : Mat3).transpose * (codeMat 212 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s90_source_le :
    step113_415ActualSource90 ≤ actionW (codeMat 142) (codeMat 86) orbit29W := by
  apply step113_415_spanCodes_le_of_gens [273, 144, 89, 49, 4, 2]
    (actionW (codeMat 142) (codeMat 86) orbit29W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 161 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 161 (by decide)
    have hact : actionA (codeMat 142) (codeMat 86) (codeMat 161) = codeMat 273 := by
      unfold actionA; rw [step113_415s90_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 161 * (codeMat 212 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 3 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 3 (by decide)
    have hact : actionA (codeMat 142) (codeMat 86) (codeMat 3) = codeMat 144 := by
      unfold actionA; rw [step113_415s90_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 3 * (codeMat 212 : Mat3).transpose = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 228 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 228 (by decide)
    have hact : actionA (codeMat 142) (codeMat 86) (codeMat 228) = codeMat 89 := by
      unfold actionA; rw [step113_415s90_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 228 * (codeMat 212 : Mat3).transpose = codeMat 89
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 160 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 160 (by decide)
    have hact : actionA (codeMat 142) (codeMat 86) (codeMat 160) = codeMat 49 := by
      unfold actionA; rw [step113_415s90_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 160 * (codeMat 212 : Mat3).transpose = codeMat 49
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 8 (by decide)
    have hact : actionA (codeMat 142) (codeMat 86) (codeMat 8) = codeMat 4 := by
      unfold actionA; rw [step113_415s90_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 8 * (codeMat 212 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 24 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 24 (by decide)
    have hact : actionA (codeMat 142) (codeMat 86) (codeMat 24) = codeMat 2 := by
      unfold actionA; rw [step113_415s90_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 24 * (codeMat 212 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row90_qr : QuotientRankAtLeast step113_415ActualSource90 15 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 86 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 86) orbit29W) 15 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 86) hP hQ orbit29W 15 QiushiMatmul.orbit29_lb15
  exact quotientRankAtLeast_mono step113_415s90_source_le hAct

-- Source 91: row 781, orbit 35, lb 15, cap 1
def step113_415ActualSource91 : Submodule F2 Mat3 := spanCodes [256, 160, 97, 17, 4, 2]

theorem step113_415_row91_W_le_source : o415W ≤ step113_415ActualSource91 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource91
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 97, 17, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 97, 17, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 97, 17, 4, 2] 2 (by decide)

private theorem step113_415s91_QtInv :
    (codeMat 165 : Mat3).transpose⁻¹ = (codeMat 163 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 165 : Mat3).transpose * (codeMat 163 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s91_source_le :
    step113_415ActualSource91 ≤ transposeW (actionW (codeMat 212) (codeMat 165) orbit35W) := by
  apply step113_415_spanCodes_le_of_gens [256, 160, 97, 17, 4, 2]
    (transposeW (actionW (codeMat 212) (codeMat 165) orbit35W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 3 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 3 (by decide)
    have hact : actionA (codeMat 212) (codeMat 165) (codeMat 3) = codeMat 256 := by
      unfold actionA; rw [step113_415s91_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 3 * (codeMat 163 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 256 ∈ actionW (codeMat 212) (codeMat 165) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 256 : Mat3).transpose = codeMat 256 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h1
    have hw : codeMat 28 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 28 (by decide)
    have hact : actionA (codeMat 212) (codeMat 165) (codeMat 28) = codeMat 160 := by
      unfold actionA; rw [step113_415s91_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 28 * (codeMat 163 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 160 ∈ actionW (codeMat 212) (codeMat 165) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 160 : Mat3).transpose = codeMat 160 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h2
    have hw : codeMat 148 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 148 (by decide)
    have hact : actionA (codeMat 212) (codeMat 165) (codeMat 148) = codeMat 133 := by
      unfold actionA; rw [step113_415s91_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 148 * (codeMat 163 : Mat3).transpose = codeMat 133
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 133 ∈ actionW (codeMat 212) (codeMat 165) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 133 : Mat3).transpose = codeMat 97 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h3
    have hw : codeMat 104 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 104 (by decide)
    have hact : actionA (codeMat 212) (codeMat 165) (codeMat 104) = codeMat 17 := by
      unfold actionA; rw [step113_415s91_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 104 * (codeMat 163 : Mat3).transpose = codeMat 17
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 17 ∈ actionW (codeMat 212) (codeMat 165) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 17 : Mat3).transpose = codeMat 17 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h4
    have hw : codeMat 1 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 1 (by decide)
    have hact : actionA (codeMat 212) (codeMat 165) (codeMat 1) = codeMat 64 := by
      unfold actionA; rw [step113_415s91_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 1 * (codeMat 163 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 64 ∈ actionW (codeMat 212) (codeMat 165) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 64 : Mat3).transpose = codeMat 4 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h5
    have hw : codeMat 8 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 8 (by decide)
    have hact : actionA (codeMat 212) (codeMat 165) (codeMat 8) = codeMat 8 := by
      unfold actionA; rw [step113_415s91_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 8 * (codeMat 163 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 8 ∈ actionW (codeMat 212) (codeMat 165) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 8 : Mat3).transpose = codeMat 2 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans

theorem step113_415_row91_qr : QuotientRankAtLeast step113_415ActualSource91 15 := by
  have hP : Invertible (codeMat 212 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 165 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 212) (codeMat 165) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 212) (codeMat 165) hP hQ orbit35W 15 QiushiMatmul.orbit35_lb15
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 212) (codeMat 165) orbit35W)) 15 :=
    quotientRankAtLeast_transpose hAct
  exact quotientRankAtLeast_mono step113_415s91_source_le hT

-- Source 92: row 790, orbit 35, lb 15, cap 1
def step113_415ActualSource92 : Submodule F2 Mat3 := spanCodes [257, 129, 97, 16, 4, 2]

theorem step113_415_row92_W_le_source : o415W ≤ step113_415ActualSource92 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource92
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [257, 129, 97, 16, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [257, 129, 97, 16, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [257, 129, 97, 16, 4, 2] 2 (by decide)

private theorem step113_415s92_QtInv :
    (codeMat 124 : Mat3).transpose⁻¹ = (codeMat 124 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 124 : Mat3).transpose * (codeMat 124 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s92_source_le :
    step113_415ActualSource92 ≤ actionW (codeMat 161) (codeMat 124) orbit35W := by
  apply step113_415_spanCodes_le_of_gens [257, 129, 97, 16, 4, 2]
    (actionW (codeMat 161) (codeMat 124) orbit35W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 30 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 30 (by decide)
    have hact : actionA (codeMat 161) (codeMat 124) (codeMat 30) = codeMat 257 := by
      unfold actionA; rw [step113_415s92_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 30 * (codeMat 124 : Mat3).transpose = codeMat 257
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 22 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 22 (by decide)
    have hact : actionA (codeMat 161) (codeMat 124) (codeMat 22) = codeMat 129 := by
      unfold actionA; rw [step113_415s92_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 22 * (codeMat 124 : Mat3).transpose = codeMat 129
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 246 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 246 (by decide)
    have hact : actionA (codeMat 161) (codeMat 124) (codeMat 246) = codeMat 97 := by
      unfold actionA; rw [step113_415s92_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 246 * (codeMat 124 : Mat3).transpose = codeMat 97
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 128 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 128 (by decide)
    have hact : actionA (codeMat 161) (codeMat 124) (codeMat 128) = codeMat 16 := by
      unfold actionA; rw [step113_415s92_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 128 * (codeMat 124 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 3 (by decide)
    have hact : actionA (codeMat 161) (codeMat 124) (codeMat 3) = codeMat 4 := by
      unfold actionA; rw [step113_415s92_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 3 * (codeMat 124 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 124) (codeMat 2) = codeMat 2 := by
      unfold actionA; rw [step113_415s92_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 124 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row92_qr : QuotientRankAtLeast step113_415ActualSource92 15 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 124 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 124) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 124) hP hQ orbit35W 15 QiushiMatmul.orbit35_lb15
  exact quotientRankAtLeast_mono step113_415s92_source_le hAct

-- Source 93: row 791, orbit 35, lb 15, cap 1
def step113_415ActualSource93 : Submodule F2 Mat3 := spanCodes [256, 129, 96, 17, 4, 2]

theorem step113_415_row93_W_le_source : o415W ≤ step113_415ActualSource93 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource93
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 129, 96, 17, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 129, 96, 17, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 129, 96, 17, 4, 2] 2 (by decide)

private theorem step113_415s93_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s93_source_le :
    step113_415ActualSource93 ≤ actionW (codeMat 417) (codeMat 84) orbit35W := by
  apply step113_415_spanCodes_le_of_gens [256, 129, 96, 17, 4, 2]
    (actionW (codeMat 417) (codeMat 84) orbit35W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 8 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 8 (by decide)
    have hact : actionA (codeMat 417) (codeMat 84) (codeMat 8) = codeMat 256 := by
      unfold actionA; rw [step113_415s93_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 8 * (codeMat 84 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 20 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 20 (by decide)
    have hact : actionA (codeMat 417) (codeMat 84) (codeMat 20) = codeMat 129 := by
      unfold actionA; rw [step113_415s93_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 20 * (codeMat 84 : Mat3).transpose = codeMat 129
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 104 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 104 (by decide)
    have hact : actionA (codeMat 417) (codeMat 84) (codeMat 104) = codeMat 96 := by
      unfold actionA; rw [step113_415s93_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 104 * (codeMat 84 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 148 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 148 (by decide)
    have hact : actionA (codeMat 417) (codeMat 84) (codeMat 148) = codeMat 17 := by
      unfold actionA; rw [step113_415s93_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 148 * (codeMat 84 : Mat3).transpose = codeMat 17
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 1 (by decide)
    have hact : actionA (codeMat 417) (codeMat 84) (codeMat 1) = codeMat 4 := by
      unfold actionA; rw [step113_415s93_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 1 * (codeMat 84 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 2 (by decide)
    have hact : actionA (codeMat 417) (codeMat 84) (codeMat 2) = codeMat 2 := by
      unfold actionA; rw [step113_415s93_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 2 * (codeMat 84 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row93_qr : QuotientRankAtLeast step113_415ActualSource93 15 := by
  have hP : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 417) (codeMat 84) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 417) (codeMat 84) hP hQ orbit35W 15 QiushiMatmul.orbit35_lb15
  exact quotientRankAtLeast_mono step113_415s93_source_le hAct

-- Source 94: row 793, orbit 35, lb 15, cap 1
def step113_415ActualSource94 : Submodule F2 Mat3 := spanCodes [273, 145, 65, 33, 4, 2]

theorem step113_415_row94_W_le_source : o415W ≤ step113_415ActualSource94 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource94
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 145, 65, 33, 4, 2] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 145, 65, 33, 4, 2] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [273, 145, 65, 33, 4, 2] 2 (by decide)

private theorem step113_415s94_QtInv :
    (codeMat 181 : Mat3).transpose⁻¹ = (codeMat 423 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 181 : Mat3).transpose * (codeMat 423 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s94_source_le :
    step113_415ActualSource94 ≤ transposeW (actionW (codeMat 86) (codeMat 181) orbit35W) := by
  apply step113_415_spanCodes_le_of_gens [273, 145, 65, 33, 4, 2]
    (transposeW (actionW (codeMat 86) (codeMat 181) orbit35W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 107 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 107 (by decide)
    have hact : actionA (codeMat 86) (codeMat 181) (codeMat 107) = codeMat 273 := by
      unfold actionA; rw [step113_415s94_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 107 * (codeMat 423 : Mat3).transpose = codeMat 273
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 273 ∈ actionW (codeMat 86) (codeMat 181) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 273 : Mat3).transpose = codeMat 273 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h1
    have hw : codeMat 104 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 104 (by decide)
    have hact : actionA (codeMat 86) (codeMat 181) (codeMat 104) = codeMat 49 := by
      unfold actionA; rw [step113_415s94_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 104 * (codeMat 423 : Mat3).transpose = codeMat 49
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 49 ∈ actionW (codeMat 86) (codeMat 181) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 49 : Mat3).transpose = codeMat 145 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h2
    have hw : codeMat 128 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 128 (by decide)
    have hact : actionA (codeMat 86) (codeMat 181) (codeMat 128) = codeMat 5 := by
      unfold actionA; rw [step113_415s94_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 128 * (codeMat 423 : Mat3).transpose = codeMat 5
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 5 ∈ actionW (codeMat 86) (codeMat 181) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 5 : Mat3).transpose = codeMat 65 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h3
    have hw : codeMat 118 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 118 (by decide)
    have hact : actionA (codeMat 86) (codeMat 181) (codeMat 118) = codeMat 129 := by
      unfold actionA; rw [step113_415s94_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 118 * (codeMat 423 : Mat3).transpose = codeMat 129
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 129 ∈ actionW (codeMat 86) (codeMat 181) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 129 : Mat3).transpose = codeMat 33 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h4
    have hw : codeMat 9 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 9 (by decide)
    have hact : actionA (codeMat 86) (codeMat 181) (codeMat 9) = codeMat 64 := by
      unfold actionA; rw [step113_415s94_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 9 * (codeMat 423 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 64 ∈ actionW (codeMat 86) (codeMat 181) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 64 : Mat3).transpose = codeMat 4 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans
  · subst h5
    have hw : codeMat 8 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 8 (by decide)
    have hact : actionA (codeMat 86) (codeMat 181) (codeMat 8) = codeMat 8 := by
      unfold actionA; rw [step113_415s94_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 8 * (codeMat 423 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmA : codeMat 8 ∈ actionW (codeMat 86) (codeMat 181) orbit35W :=
      step113_415_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 8 : Mat3).transpose = codeMat 2 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_transposeW_of_witness hmA htrans

theorem step113_415_row94_qr : QuotientRankAtLeast step113_415ActualSource94 15 := by
  have hP : Invertible (codeMat 86 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 181 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 86) (codeMat 181) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 86) (codeMat 181) hP hQ orbit35W 15 QiushiMatmul.orbit35_lb15
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 86) (codeMat 181) orbit35W)) 15 :=
    quotientRankAtLeast_transpose hAct
  exact quotientRankAtLeast_mono step113_415s94_source_le hT

-- Source 95: row 1919, orbit 5, lb 9, cap 7
def step113_415ActualSource95 : Submodule F2 Mat3 := spanCodes [272, 152, 72, 56, 4, 2, 1]

theorem step113_415_row95_W_le_source : o415W ≤ step113_415ActualSource95 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource95
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 152, 72, 56, 4, 2, 1] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 152, 72, 56, 4, 2, 1] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 152, 72, 56, 4, 2, 1] 2 (by decide)

private theorem step113_415s95_QtInv :
    (codeMat 409 : Mat3).transpose⁻¹ = (codeMat 473 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 409 : Mat3).transpose * (codeMat 473 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s95_source_le :
    step113_415ActualSource95 ≤ actionW (codeMat 177) (codeMat 409) orbit5W := by
  apply step113_415_spanCodes_le_of_gens [272, 152, 72, 56, 4, 2, 1]
    (actionW (codeMat 177) (codeMat 409) orbit5W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 160 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 160 (by decide)
    have hact : actionA (codeMat 177) (codeMat 409) (codeMat 160) = codeMat 272 := by
      unfold actionA; rw [step113_415s95_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 160 * (codeMat 473 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 240 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 240 (by decide)
    have hact : actionA (codeMat 177) (codeMat 409) (codeMat 240) = codeMat 152 := by
      unfold actionA; rw [step113_415s95_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 240 * (codeMat 473 : Mat3).transpose = codeMat 152
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 24 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 24 (by decide)
    have hact : actionA (codeMat 177) (codeMat 409) (codeMat 24) = codeMat 72 := by
      unfold actionA; rw [step113_415s95_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 24 * (codeMat 473 : Mat3).transpose = codeMat 72
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 64 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 64 (by decide)
    have hact : actionA (codeMat 177) (codeMat 409) (codeMat 64) = codeMat 56 := by
      unfold actionA; rw [step113_415s95_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 64 * (codeMat 473 : Mat3).transpose = codeMat 56
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 4 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 4 (by decide)
    have hact : actionA (codeMat 177) (codeMat 409) (codeMat 4) = codeMat 4 := by
      unfold actionA; rw [step113_415s95_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 4 * (codeMat 473 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 6 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 6 (by decide)
    have hact : actionA (codeMat 177) (codeMat 409) (codeMat 6) = codeMat 2 := by
      unfold actionA; rw [step113_415s95_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 6 * (codeMat 473 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 3 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 3 (by decide)
    have hact : actionA (codeMat 177) (codeMat 409) (codeMat 3) = codeMat 1 := by
      unfold actionA; rw [step113_415s95_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 3 * (codeMat 473 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row95_qr : QuotientRankAtLeast step113_415ActualSource95 9 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 409 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 409) orbit5W) 9 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 409) hP hQ orbit5W 9 QiushiMatmul.orbit5_lb9
  exact quotientRankAtLeast_mono step113_415s95_source_le hAct

-- Source 96: row 1921, orbit 5, lb 9, cap 7
def step113_415ActualSource96 : Submodule F2 Mat3 := spanCodes [272, 160, 64, 8, 4, 2, 1]

theorem step113_415_row96_W_le_source : o415W ≤ step113_415ActualSource96 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource96
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 160, 64, 8, 4, 2, 1] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 160, 64, 8, 4, 2, 1] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 160, 64, 8, 4, 2, 1] 2 (by decide)

private theorem step113_415s96_QtInv :
    (codeMat 401 : Mat3).transpose⁻¹ = (codeMat 401 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 401 : Mat3).transpose * (codeMat 401 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s96_source_le :
    step113_415ActualSource96 ≤ actionW (codeMat 177) (codeMat 401) orbit5W := by
  apply step113_415_spanCodes_le_of_gens [272, 160, 64, 8, 4, 2, 1]
    (actionW (codeMat 177) (codeMat 401) orbit5W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 160 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 160 (by decide)
    have hact : actionA (codeMat 177) (codeMat 401) (codeMat 160) = codeMat 272 := by
      unfold actionA; rw [step113_415s96_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 160 * (codeMat 401 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 176 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 176 (by decide)
    have hact : actionA (codeMat 177) (codeMat 401) (codeMat 176) = codeMat 160 := by
      unfold actionA; rw [step113_415s96_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 176 * (codeMat 401 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 72 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 72 (by decide)
    have hact : actionA (codeMat 177) (codeMat 401) (codeMat 72) = codeMat 64 := by
      unfold actionA; rw [step113_415s96_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 72 * (codeMat 401 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 64 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 64 (by decide)
    have hact : actionA (codeMat 177) (codeMat 401) (codeMat 64) = codeMat 8 := by
      unfold actionA; rw [step113_415s96_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 64 * (codeMat 401 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 4 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 4 (by decide)
    have hact : actionA (codeMat 177) (codeMat 401) (codeMat 4) = codeMat 4 := by
      unfold actionA; rw [step113_415s96_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 4 * (codeMat 401 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 6 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 6 (by decide)
    have hact : actionA (codeMat 177) (codeMat 401) (codeMat 6) = codeMat 2 := by
      unfold actionA; rw [step113_415s96_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 6 * (codeMat 401 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 1 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 401) (codeMat 1) = codeMat 1 := by
      unfold actionA; rw [step113_415s96_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * (codeMat 401 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row96_qr : QuotientRankAtLeast step113_415ActualSource96 9 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 401) orbit5W) 9 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 401) hP hQ orbit5W 9 QiushiMatmul.orbit5_lb9
  exact quotientRankAtLeast_mono step113_415s96_source_le hAct

-- Source 97: row 1928, orbit 5, lb 9, cap 7
def step113_415ActualSource97 : Submodule F2 Mat3 := spanCodes [264, 200, 32, 24, 4, 2, 1]

theorem step113_415_row97_W_le_source : o415W ≤ step113_415ActualSource97 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource97
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [264, 200, 32, 24, 4, 2, 1] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [264, 200, 32, 24, 4, 2, 1] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [264, 200, 32, 24, 4, 2, 1] 2 (by decide)

private theorem step113_415s97_QtInv :
    (codeMat 233 : Mat3).transpose⁻¹ = (codeMat 233 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 233 : Mat3).transpose * (codeMat 233 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s97_source_le :
    step113_415ActualSource97 ≤ actionW (codeMat 273) (codeMat 233) orbit5W := by
  apply step113_415_spanCodes_le_of_gens [264, 200, 32, 24, 4, 2, 1]
    (actionW (codeMat 273) (codeMat 233) orbit5W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 184 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 184 (by decide)
    have hact : actionA (codeMat 273) (codeMat 233) (codeMat 184) = codeMat 264 := by
      unfold actionA; rw [step113_415s97_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 184 * (codeMat 233 : Mat3).transpose = codeMat 264
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 248 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 248 (by decide)
    have hact : actionA (codeMat 273) (codeMat 233) (codeMat 248) = codeMat 200 := by
      unfold actionA; rw [step113_415s97_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 248 * (codeMat 233 : Mat3).transpose = codeMat 200
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 16 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 16 (by decide)
    have hact : actionA (codeMat 273) (codeMat 233) (codeMat 16) = codeMat 32 := by
      unfold actionA; rw [step113_415s97_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 16 * (codeMat 233 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 24 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 24 (by decide)
    have hact : actionA (codeMat 273) (codeMat 233) (codeMat 24) = codeMat 24 := by
      unfold actionA; rw [step113_415s97_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 24 * (codeMat 233 : Mat3).transpose = codeMat 24
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 233) (codeMat 2) = codeMat 4 := by
      unfold actionA; rw [step113_415s97_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 233 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 4 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 4 (by decide)
    have hact : actionA (codeMat 273) (codeMat 233) (codeMat 4) = codeMat 2 := by
      unfold actionA; rw [step113_415s97_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 4 * (codeMat 233 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 7 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 7 (by decide)
    have hact : actionA (codeMat 273) (codeMat 233) (codeMat 7) = codeMat 1 := by
      unfold actionA; rw [step113_415s97_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 7 * (codeMat 233 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row97_qr : QuotientRankAtLeast step113_415ActualSource97 9 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 233 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 233) orbit5W) 9 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 233) hP hQ orbit5W 9 QiushiMatmul.orbit5_lb9
  exact quotientRankAtLeast_mono step113_415s97_source_le hAct

-- Source 98: row 2007, orbit 7, lb 9, cap 7
def step113_415ActualSource98 : Submodule F2 Mat3 := spanCodes [272, 160, 112, 8, 4, 2, 1]

theorem step113_415_row98_W_le_source : o415W ≤ step113_415ActualSource98 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource98
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 160, 112, 8, 4, 2, 1] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 160, 112, 8, 4, 2, 1] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 160, 112, 8, 4, 2, 1] 2 (by decide)

private theorem step113_415s98_QtInv :
    (codeMat 498 : Mat3).transpose⁻¹ = (codeMat 206 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 498 : Mat3).transpose * (codeMat 206 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s98_source_le :
    step113_415ActualSource98 ≤ actionW (codeMat 177) (codeMat 498) flatW_7 := by
  apply step113_415_spanCodes_le_of_gens [272, 160, 112, 8, 4, 2, 1]
    (actionW (codeMat 177) (codeMat 498) flatW_7)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 112 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 112 (by decide)
    have hact : actionA (codeMat 177) (codeMat 498) (codeMat 112) = codeMat 272 := by
      unfold actionA; rw [step113_415s98_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 112 * (codeMat 206 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 120 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 120 (by decide)
    have hact : actionA (codeMat 177) (codeMat 498) (codeMat 120) = codeMat 160 := by
      unfold actionA; rw [step113_415s98_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 120 * (codeMat 206 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 352 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 352 (by decide)
    have hact : actionA (codeMat 177) (codeMat 498) (codeMat 352) = codeMat 112 := by
      unfold actionA; rw [step113_415s98_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 352 * (codeMat 206 : Mat3).transpose = codeMat 112
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 177) (codeMat 498) (codeMat 256) = codeMat 8 := by
      unfold actionA; rw [step113_415s98_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 256 * (codeMat 206 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 6 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 6 (by decide)
    have hact : actionA (codeMat 177) (codeMat 498) (codeMat 6) = codeMat 4 := by
      unfold actionA; rw [step113_415s98_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 6 * (codeMat 206 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 7 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 7 (by decide)
    have hact : actionA (codeMat 177) (codeMat 498) (codeMat 7) = codeMat 2 := by
      unfold actionA; rw [step113_415s98_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 7 * (codeMat 206 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 4 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 4 (by decide)
    have hact : actionA (codeMat 177) (codeMat 498) (codeMat 4) = codeMat 1 := by
      unfold actionA; rw [step113_415s98_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 4 * (codeMat 206 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row98_qr : QuotientRankAtLeast step113_415ActualSource98 9 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 498 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 498) flatW_7) 9 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 498) hP hQ flatW_7 9 QiushiMatmul.flatSeed_7
  exact quotientRankAtLeast_mono step113_415s98_source_le hAct

-- Source 99: row 2012, orbit 7, lb 9, cap 7
def step113_415ActualSource99 : Submodule F2 Mat3 := spanCodes [272, 152, 64, 56, 4, 2, 1]

theorem step113_415_row99_W_le_source : o415W ≤ step113_415ActualSource99 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource99
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 152, 64, 56, 4, 2, 1] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 152, 64, 56, 4, 2, 1] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 152, 64, 56, 4, 2, 1] 2 (by decide)

private theorem step113_415s99_QtInv :
    (codeMat 499 : Mat3).transpose⁻¹ = (codeMat 382 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 499 : Mat3).transpose * (codeMat 382 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s99_source_le :
    step113_415ActualSource99 ≤ actionW (codeMat 177) (codeMat 499) flatW_7 := by
  apply step113_415_spanCodes_le_of_gens [272, 152, 64, 56, 4, 2, 1]
    (actionW (codeMat 177) (codeMat 499) flatW_7)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 112 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 112 (by decide)
    have hact : actionA (codeMat 177) (codeMat 499) (codeMat 112) = codeMat 272 := by
      unfold actionA; rw [step113_415s99_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 112 * (codeMat 382 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 376 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 376 (by decide)
    have hact : actionA (codeMat 177) (codeMat 499) (codeMat 376) = codeMat 152 := by
      unfold actionA; rw [step113_415s99_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 376 * (codeMat 382 : Mat3).transpose = codeMat 152
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 360 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 360 (by decide)
    have hact : actionA (codeMat 177) (codeMat 499) (codeMat 360) = codeMat 64 := by
      unfold actionA; rw [step113_415s99_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 360 * (codeMat 382 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 177) (codeMat 499) (codeMat 256) = codeMat 56 := by
      unfold actionA; rw [step113_415s99_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 256 * (codeMat 382 : Mat3).transpose = codeMat 56
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 6 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 6 (by decide)
    have hact : actionA (codeMat 177) (codeMat 499) (codeMat 6) = codeMat 4 := by
      unfold actionA; rw [step113_415s99_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 6 * (codeMat 382 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 7 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 7 (by decide)
    have hact : actionA (codeMat 177) (codeMat 499) (codeMat 7) = codeMat 2 := by
      unfold actionA; rw [step113_415s99_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 7 * (codeMat 382 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 5 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 5 (by decide)
    have hact : actionA (codeMat 177) (codeMat 499) (codeMat 5) = codeMat 1 := by
      unfold actionA; rw [step113_415s99_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 5 * (codeMat 382 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row99_qr : QuotientRankAtLeast step113_415ActualSource99 9 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 499 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 499) flatW_7) 9 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 499) hP hQ flatW_7 9 QiushiMatmul.flatSeed_7
  exact quotientRankAtLeast_mono step113_415s99_source_le hAct

-- Source 100: row 2090, orbit 7, lb 9, cap 7
def step113_415ActualSource100 : Submodule F2 Mat3 := spanCodes [272, 208, 32, 8, 4, 2, 1]

theorem step113_415_row100_W_le_source : o415W ≤ step113_415ActualSource100 := by
  unfold o415W
  apply step113_415_spanCodes_le_of_gens [273, 4, 2] step113_415ActualSource100
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 208, 32, 8, 4, 2, 1] 273 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 208, 32, 8, 4, 2, 1] 4 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 208, 32, 8, 4, 2, 1] 2 (by decide)

private theorem step113_415s100_QtInv :
    (codeMat 157 : Mat3).transpose⁻¹ = (codeMat 486 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 157 : Mat3).transpose * (codeMat 486 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step113_415s100_source_le :
    step113_415ActualSource100 ≤ actionW (codeMat 273) (codeMat 157) flatW_7 := by
  apply step113_415_spanCodes_le_of_gens [272, 208, 32, 8, 4, 2, 1]
    (actionW (codeMat 273) (codeMat 157) flatW_7)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 112 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 112 (by decide)
    have hact : actionA (codeMat 273) (codeMat 157) (codeMat 112) = codeMat 272 := by
      unfold actionA; rw [step113_415s100_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 112 * (codeMat 486 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 368 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 368 (by decide)
    have hact : actionA (codeMat 273) (codeMat 157) (codeMat 368) = codeMat 208 := by
      unfold actionA; rw [step113_415s100_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 368 * (codeMat 486 : Mat3).transpose = codeMat 208
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 157) (codeMat 8) = codeMat 32 := by
      unfold actionA; rw [step113_415s100_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 486 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 24 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 24 (by decide)
    have hact : actionA (codeMat 273) (codeMat 157) (codeMat 24) = codeMat 8 := by
      unfold actionA; rw [step113_415s100_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 24 * (codeMat 486 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 157) (codeMat 1) = codeMat 4 := by
      unfold actionA; rw [step113_415s100_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 486 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 6 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 6 (by decide)
    have hact : actionA (codeMat 273) (codeMat 157) (codeMat 6) = codeMat 2 := by
      unfold actionA; rw [step113_415s100_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 6 * (codeMat 486 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 3 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 273) (codeMat 157) (codeMat 3) = codeMat 1 := by
      unfold actionA; rw [step113_415s100_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 3 * (codeMat 486 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step113_415_codeMat_mem_actionW_of_witness hw hact

theorem step113_415_row100_qr : QuotientRankAtLeast step113_415ActualSource100 9 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 157 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 157) flatW_7) 9 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 157) hP hQ flatW_7 9 QiushiMatmul.flatSeed_7
  exact quotientRankAtLeast_mono step113_415s100_source_le hAct

/-- All 101 source row lower bounds. -/
theorem step113_415_row_qr (i : Fin 101) : QuotientRankAtLeast
    (match i.val with
    | 0 => step113_415ActualSource0
    | 1 => step113_415ActualSource1
    | 2 => step113_415ActualSource2
    | 3 => step113_415ActualSource3
    | 4 => step113_415ActualSource4
    | 5 => step113_415ActualSource5
    | 6 => step113_415ActualSource6
    | 7 => step113_415ActualSource7
    | 8 => step113_415ActualSource8
    | 9 => step113_415ActualSource9
    | 10 => step113_415ActualSource10
    | 11 => step113_415ActualSource11
    | 12 => step113_415ActualSource12
    | 13 => step113_415ActualSource13
    | 14 => step113_415ActualSource14
    | 15 => step113_415ActualSource15
    | 16 => step113_415ActualSource16
    | 17 => step113_415ActualSource17
    | 18 => step113_415ActualSource18
    | 19 => step113_415ActualSource19
    | 20 => step113_415ActualSource20
    | 21 => step113_415ActualSource21
    | 22 => step113_415ActualSource22
    | 23 => step113_415ActualSource23
    | 24 => step113_415ActualSource24
    | 25 => step113_415ActualSource25
    | 26 => step113_415ActualSource26
    | 27 => step113_415ActualSource27
    | 28 => step113_415ActualSource28
    | 29 => step113_415ActualSource29
    | 30 => step113_415ActualSource30
    | 31 => step113_415ActualSource31
    | 32 => step113_415ActualSource32
    | 33 => step113_415ActualSource33
    | 34 => step113_415ActualSource34
    | 35 => step113_415ActualSource35
    | 36 => step113_415ActualSource36
    | 37 => step113_415ActualSource37
    | 38 => step113_415ActualSource38
    | 39 => step113_415ActualSource39
    | 40 => step113_415ActualSource40
    | 41 => step113_415ActualSource41
    | 42 => step113_415ActualSource42
    | 43 => step113_415ActualSource43
    | 44 => step113_415ActualSource44
    | 45 => step113_415ActualSource45
    | 46 => step113_415ActualSource46
    | 47 => step113_415ActualSource47
    | 48 => step113_415ActualSource48
    | 49 => step113_415ActualSource49
    | 50 => step113_415ActualSource50
    | 51 => step113_415ActualSource51
    | 52 => step113_415ActualSource52
    | 53 => step113_415ActualSource53
    | 54 => step113_415ActualSource54
    | 55 => step113_415ActualSource55
    | 56 => step113_415ActualSource56
    | 57 => step113_415ActualSource57
    | 58 => step113_415ActualSource58
    | 59 => step113_415ActualSource59
    | 60 => step113_415ActualSource60
    | 61 => step113_415ActualSource61
    | 62 => step113_415ActualSource62
    | 63 => step113_415ActualSource63
    | 64 => step113_415ActualSource64
    | 65 => step113_415ActualSource65
    | 66 => step113_415ActualSource66
    | 67 => step113_415ActualSource67
    | 68 => step113_415ActualSource68
    | 69 => step113_415ActualSource69
    | 70 => step113_415ActualSource70
    | 71 => step113_415ActualSource71
    | 72 => step113_415ActualSource72
    | 73 => step113_415ActualSource73
    | 74 => step113_415ActualSource74
    | 75 => step113_415ActualSource75
    | 76 => step113_415ActualSource76
    | 77 => step113_415ActualSource77
    | 78 => step113_415ActualSource78
    | 79 => step113_415ActualSource79
    | 80 => step113_415ActualSource80
    | 81 => step113_415ActualSource81
    | 82 => step113_415ActualSource82
    | 83 => step113_415ActualSource83
    | 84 => step113_415ActualSource84
    | 85 => step113_415ActualSource85
    | 86 => step113_415ActualSource86
    | 87 => step113_415ActualSource87
    | 88 => step113_415ActualSource88
    | 89 => step113_415ActualSource89
    | 90 => step113_415ActualSource90
    | 91 => step113_415ActualSource91
    | 92 => step113_415ActualSource92
    | 93 => step113_415ActualSource93
    | 94 => step113_415ActualSource94
    | 95 => step113_415ActualSource95
    | 96 => step113_415ActualSource96
    | 97 => step113_415ActualSource97
    | 98 => step113_415ActualSource98
    | 99 => step113_415ActualSource99
    | 100 => step113_415ActualSource100
    | _ => step113_415ActualSource0)
    (match i.val with
    | 0 => 15
    | 1 => 15
    | 2 => 15
    | 3 => 15
    | 4 => 15
    | 5 => 15
    | 6 => 15
    | 7 => 15
    | 8 => 11
    | 9 => 11
    | 10 => 11
    | 11 => 11
    | 12 => 11
    | 13 => 11
    | 14 => 11
    | 15 => 15
    | 16 => 15
    | 17 => 15
    | 18 => 15
    | 19 => 15
    | 20 => 15
    | 21 => 15
    | 22 => 15
    | 23 => 15
    | 24 => 15
    | 25 => 15
    | 26 => 15
    | 27 => 15
    | 28 => 15
    | 29 => 15
    | 30 => 15
    | 31 => 15
    | 32 => 15
    | 33 => 15
    | 34 => 15
    | 35 => 15
    | 36 => 15
    | 37 => 15
    | 38 => 15
    | 39 => 15
    | 40 => 15
    | 41 => 15
    | 42 => 12
    | 43 => 6
    | 44 => 6
    | 45 => 6
    | 46 => 15
    | 47 => 15
    | 48 => 15
    | 49 => 15
    | 50 => 15
    | 51 => 15
    | 52 => 15
    | 53 => 15
    | 54 => 15
    | 55 => 15
    | 56 => 15
    | 57 => 15
    | 58 => 15
    | 59 => 15
    | 60 => 15
    | 61 => 15
    | 62 => 15
    | 63 => 15
    | 64 => 15
    | 65 => 15
    | 66 => 15
    | 67 => 15
    | 68 => 9
    | 69 => 9
    | 70 => 9
    | 71 => 9
    | 72 => 9
    | 73 => 12
    | 74 => 12
    | 75 => 12
    | 76 => 12
    | 77 => 15
    | 78 => 15
    | 79 => 15
    | 80 => 15
    | 81 => 15
    | 82 => 15
    | 83 => 15
    | 84 => 15
    | 85 => 15
    | 86 => 15
    | 87 => 15
    | 88 => 15
    | 89 => 15
    | 90 => 15
    | 91 => 15
    | 92 => 15
    | 93 => 15
    | 94 => 15
    | 95 => 9
    | 96 => 9
    | 97 => 9
    | 98 => 9
    | 99 => 9
    | 100 => 9
    | _ => 15) := by
  fin_cases i
  · exact step113_415_row0_qr
  · exact step113_415_row1_qr
  · exact step113_415_row2_qr
  · exact step113_415_row3_qr
  · exact step113_415_row4_qr
  · exact step113_415_row5_qr
  · exact step113_415_row6_qr
  · exact step113_415_row7_qr
  · exact step113_415_row8_qr
  · exact step113_415_row9_qr
  · exact step113_415_row10_qr
  · exact step113_415_row11_qr
  · exact step113_415_row12_qr
  · exact step113_415_row13_qr
  · exact step113_415_row14_qr
  · exact step113_415_row15_qr
  · exact step113_415_row16_qr
  · exact step113_415_row17_qr
  · exact step113_415_row18_qr
  · exact step113_415_row19_qr
  · exact step113_415_row20_qr
  · exact step113_415_row21_qr
  · exact step113_415_row22_qr
  · exact step113_415_row23_qr
  · exact step113_415_row24_qr
  · exact step113_415_row25_qr
  · exact step113_415_row26_qr
  · exact step113_415_row27_qr
  · exact step113_415_row28_qr
  · exact step113_415_row29_qr
  · exact step113_415_row30_qr
  · exact step113_415_row31_qr
  · exact step113_415_row32_qr
  · exact step113_415_row33_qr
  · exact step113_415_row34_qr
  · exact step113_415_row35_qr
  · exact step113_415_row36_qr
  · exact step113_415_row37_qr
  · exact step113_415_row38_qr
  · exact step113_415_row39_qr
  · exact step113_415_row40_qr
  · exact step113_415_row41_qr
  · exact step113_415_row42_qr
  · exact step113_415_row43_qr
  · exact step113_415_row44_qr
  · exact step113_415_row45_qr
  · exact step113_415_row46_qr
  · exact step113_415_row47_qr
  · exact step113_415_row48_qr
  · exact step113_415_row49_qr
  · exact step113_415_row50_qr
  · exact step113_415_row51_qr
  · exact step113_415_row52_qr
  · exact step113_415_row53_qr
  · exact step113_415_row54_qr
  · exact step113_415_row55_qr
  · exact step113_415_row56_qr
  · exact step113_415_row57_qr
  · exact step113_415_row58_qr
  · exact step113_415_row59_qr
  · exact step113_415_row60_qr
  · exact step113_415_row61_qr
  · exact step113_415_row62_qr
  · exact step113_415_row63_qr
  · exact step113_415_row64_qr
  · exact step113_415_row65_qr
  · exact step113_415_row66_qr
  · exact step113_415_row67_qr
  · exact step113_415_row68_qr
  · exact step113_415_row69_qr
  · exact step113_415_row70_qr
  · exact step113_415_row71_qr
  · exact step113_415_row72_qr
  · exact step113_415_row73_qr
  · exact step113_415_row74_qr
  · exact step113_415_row75_qr
  · exact step113_415_row76_qr
  · exact step113_415_row77_qr
  · exact step113_415_row78_qr
  · exact step113_415_row79_qr
  · exact step113_415_row80_qr
  · exact step113_415_row81_qr
  · exact step113_415_row82_qr
  · exact step113_415_row83_qr
  · exact step113_415_row84_qr
  · exact step113_415_row85_qr
  · exact step113_415_row86_qr
  · exact step113_415_row87_qr
  · exact step113_415_row88_qr
  · exact step113_415_row89_qr
  · exact step113_415_row90_qr
  · exact step113_415_row91_qr
  · exact step113_415_row92_qr
  · exact step113_415_row93_qr
  · exact step113_415_row94_qr
  · exact step113_415_row95_qr
  · exact step113_415_row96_qr
  · exact step113_415_row97_qr
  · exact step113_415_row98_qr
  · exact step113_415_row99_qr
  · exact step113_415_row100_qr

end QiushiMatmul
