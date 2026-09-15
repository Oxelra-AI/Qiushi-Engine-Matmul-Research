import Mathlib
import QiushiCodeSpanCore
import QiushiFlattenSeeds
import QiushiMonotonicity
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiOrbit29FP
import QiushiOrbitTransport
import QiushiStep99Orbit120Dispatch
import QiushiStep99Orbit150Dispatch
import QiushiStep99Orbit65Dispatch
import QiushiTransposeTransport

set_option maxHeartbeats 800000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section

namespace QiushiMatmul

private theorem step103o279_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step103o279_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

private theorem step103o279_codeMat_mem_transposeW_of_witness
    {V : Submodule F2 Mat3} {pre tpre : Nat}
    (h_mem : codeMat tpre ∈ V)
    (h_trans : (codeMat tpre : Mat3).transpose = codeMat pre) :
    codeMat pre ∈ transposeW V := by
  change ∃ X, X ∈ V ∧ transposeLinearMap X = codeMat pre
  exact ⟨codeMat tpre, h_mem, h_trans⟩

def o279W : Submodule F2 Mat3 := spanCodes [68, 16, 10, 1]

private theorem step103o279_o279W_le_base150 : o279W ≤ spanCodes [258, 68, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

theorem step103_o279_base_lb16 : QuotientRankAtLeast o279W 16 :=
  quotientRankAtLeast_mono step103o279_o279W_le_base150 step99_orbit150_lb16_unconditional

-- Source 0: compressed row 0, orbit 150, action, lb 16
def step103o279ActualSource0 : Submodule F2 Mat3 := spanCodes [420, 68, 16, 10, 1]

private theorem step103o279_o279W_le_src0 : o279W ≤ spanCodes [420, 68, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s0_QtInv :
    (codeMat 309 : Mat3).transpose⁻¹ = (codeMat 309 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 309 : Mat3).transpose * (codeMat 309 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s0_source_le_transport :
    step103o279ActualSource0 ≤ actionW (codeMat 401) (codeMat 309) o150W := by
  apply step103o279_spanCodes_le_of_gens [420, 68, 16, 10, 1]
    (actionW (codeMat 401) (codeMat 309) o150W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 343 ∈ o150W :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 16, 10, 1] 343 (by decide)
    have hact : actionA (codeMat 401) (codeMat 309) (codeMat 343) = codeMat 420 := by
      unfold actionA
      rw [step103o279s0_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 343 * (codeMat 309 : Mat3).transpose = codeMat 420
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 79 ∈ o150W :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 16, 10, 1] 79 (by decide)
    have hact : actionA (codeMat 401) (codeMat 309) (codeMat 79) = codeMat 68 := by
      unfold actionA
      rw [step103o279s0_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 79 * (codeMat 309 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 16 ∈ o150W :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 401) (codeMat 309) (codeMat 16) = codeMat 16 := by
      unfold actionA
      rw [step103o279s0_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 16 * (codeMat 309 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 10 ∈ o150W :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 16, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 401) (codeMat 309) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step103o279s0_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 10 * (codeMat 309 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o150W :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 401) (codeMat 309) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step103o279s0_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 1 * (codeMat 309 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s0_qr :
    QuotientRankAtLeast step103o279ActualSource0 16 := by
  have hP : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 309 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 401) (codeMat 309) o150W) 16 :=
    @quotientRankAtLeast_action (codeMat 401) (codeMat 309) hP hQ o150W 16 step99_orbit150_lb16_unconditional
  exact quotientRankAtLeast_mono step103o279s0_source_le_transport hAct

-- Source 1: compressed row 1, orbit 120, action, lb 15
def step103o279ActualSource1 : Submodule F2 Mat3 := spanCodes [68, 36, 16, 10, 1]

private theorem step103o279_o279W_le_src1 : o279W ≤ spanCodes [68, 36, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s1_QtInv :
    (codeMat 226 : Mat3).transpose⁻¹ = (codeMat 141 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 226 : Mat3).transpose * (codeMat 141 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s1_source_le_transport :
    step103o279ActualSource1 ≤ actionW (codeMat 267) (codeMat 226) o120W := by
  apply step103o279_spanCodes_le_of_gens [68, 36, 16, 10, 1]
    (actionW (codeMat 267) (codeMat 226) o120W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 272 ∈ o120W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 32, 12, 2, 1] 272 (by decide)
    have hact : actionA (codeMat 267) (codeMat 226) (codeMat 272) = codeMat 68 := by
      unfold actionA
      rw [step103o279s1_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 272 * (codeMat 141 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ o120W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 32, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 267) (codeMat 226) (codeMat 2) = codeMat 36 := by
      unfold actionA
      rw [step103o279s1_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 2 * (codeMat 141 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 45 ∈ o120W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 32, 12, 2, 1] 45 (by decide)
    have hact : actionA (codeMat 267) (codeMat 226) (codeMat 45) = codeMat 16 := by
      unfold actionA
      rw [step103o279s1_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 45 * (codeMat 141 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 12 ∈ o120W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 32, 12, 2, 1] 12 (by decide)
    have hact : actionA (codeMat 267) (codeMat 226) (codeMat 12) = codeMat 10 := by
      unfold actionA
      rw [step103o279s1_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 12 * (codeMat 141 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 32 ∈ o120W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 32, 12, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 267) (codeMat 226) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step103o279s1_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 32 * (codeMat 141 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s1_qr :
    QuotientRankAtLeast step103o279ActualSource1 15 := by
  have hP : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 226 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 267) (codeMat 226) o120W) 15 :=
    @quotientRankAtLeast_action (codeMat 267) (codeMat 226) hP hQ o120W 15 step99_orbit120_lb15_unconditional
  exact quotientRankAtLeast_mono step103o279s1_source_le_transport hAct

-- Source 2: compressed row 2, orbit 120, action, lb 15
def step103o279ActualSource2 : Submodule F2 Mat3 := spanCodes [68, 38, 16, 10, 1]

private theorem step103o279_o279W_le_src2 : o279W ≤ spanCodes [68, 38, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s2_QtInv :
    (codeMat 482 : Mat3).transpose⁻¹ = (codeMat 143 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 482 : Mat3).transpose * (codeMat 143 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s2_source_le_transport :
    step103o279ActualSource2 ≤ actionW (codeMat 267) (codeMat 482) o120W := by
  apply step103o279_spanCodes_le_of_gens [68, 38, 16, 10, 1]
    (actionW (codeMat 267) (codeMat 482) o120W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 304 ∈ o120W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 32, 12, 2, 1] 304 (by decide)
    have hact : actionA (codeMat 267) (codeMat 482) (codeMat 304) = codeMat 68 := by
      unfold actionA
      rw [step103o279s2_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 304 * (codeMat 143 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 46 ∈ o120W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 32, 12, 2, 1] 46 (by decide)
    have hact : actionA (codeMat 267) (codeMat 482) (codeMat 46) = codeMat 38 := by
      unfold actionA
      rw [step103o279s2_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 46 * (codeMat 143 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 45 ∈ o120W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 32, 12, 2, 1] 45 (by decide)
    have hact : actionA (codeMat 267) (codeMat 482) (codeMat 45) = codeMat 16 := by
      unfold actionA
      rw [step103o279s2_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 45 * (codeMat 143 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 12 ∈ o120W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 32, 12, 2, 1] 12 (by decide)
    have hact : actionA (codeMat 267) (codeMat 482) (codeMat 12) = codeMat 10 := by
      unfold actionA
      rw [step103o279s2_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 12 * (codeMat 143 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 32 ∈ o120W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 32, 12, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 267) (codeMat 482) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step103o279s2_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 32 * (codeMat 143 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s2_qr :
    QuotientRankAtLeast step103o279ActualSource2 15 := by
  have hP : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 482 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 267) (codeMat 482) o120W) 15 :=
    @quotientRankAtLeast_action (codeMat 267) (codeMat 482) hP hQ o120W 15 step99_orbit120_lb15_unconditional
  exact quotientRankAtLeast_mono step103o279s2_source_le_transport hAct

-- Source 3: compressed row 3, orbit 120, transpose, lb 15
def step103o279ActualSource3 : Submodule F2 Mat3 := spanCodes [128, 68, 16, 10, 1]

private theorem step103o279_o279W_le_src3 : o279W ≤ spanCodes [128, 68, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s3_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s3_source_le_transport :
    step103o279ActualSource3 ≤ actionW (codeMat 98) (codeMat 266) (transposeW o120W) := by
  apply step103o279_spanCodes_le_of_gens [128, 68, 16, 10, 1]
    (actionW (codeMat 98) (codeMat 266) (transposeW o120W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw0 : codeMat 2 ∈ o120W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 32, 12, 2, 1] 2 (by decide)
    have hwT : (codeMat 2 : Mat3).transpose = codeMat 8 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hw : codeMat 8 ∈ transposeW o120W :=
      step103o279_codeMat_mem_transposeW_of_witness hw0 hwT
    have hact : actionA (codeMat 98) (codeMat 266) (codeMat 8) = codeMat 128 := by
      unfold actionA
      rw [step103o279s3_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 8 * (codeMat 266 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw0 : codeMat 272 ∈ o120W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 32, 12, 2, 1] 272 (by decide)
    have hwT : (codeMat 272 : Mat3).transpose = codeMat 272 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hw : codeMat 272 ∈ transposeW o120W :=
      step103o279_codeMat_mem_transposeW_of_witness hw0 hwT
    have hact : actionA (codeMat 98) (codeMat 266) (codeMat 272) = codeMat 68 := by
      unfold actionA
      rw [step103o279s3_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 272 * (codeMat 266 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw0 : codeMat 1 ∈ o120W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 32, 12, 2, 1] 1 (by decide)
    have hwT : (codeMat 1 : Mat3).transpose = codeMat 1 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hw : codeMat 1 ∈ transposeW o120W :=
      step103o279_codeMat_mem_transposeW_of_witness hw0 hwT
    have hact : actionA (codeMat 98) (codeMat 266) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step103o279s3_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw0 : codeMat 12 ∈ o120W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 32, 12, 2, 1] 12 (by decide)
    have hwT : (codeMat 12 : Mat3).transpose = codeMat 66 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hw : codeMat 66 ∈ transposeW o120W :=
      step103o279_codeMat_mem_transposeW_of_witness hw0 hwT
    have hact : actionA (codeMat 98) (codeMat 266) (codeMat 66) = codeMat 10 := by
      unfold actionA
      rw [step103o279s3_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 66 * (codeMat 266 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw0 : codeMat 32 ∈ o120W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 32, 12, 2, 1] 32 (by decide)
    have hwT : (codeMat 32 : Mat3).transpose = codeMat 128 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hw : codeMat 128 ∈ transposeW o120W :=
      step103o279_codeMat_mem_transposeW_of_witness hw0 hwT
    have hact : actionA (codeMat 98) (codeMat 266) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step103o279s3_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 128 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s3_qr :
    QuotientRankAtLeast step103o279ActualSource3 15 := by
  have hP : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hT : QuotientRankAtLeast (transposeW o120W) 15 :=
    quotientRankAtLeast_transpose step99_orbit120_lb15_unconditional
  have hAct : QuotientRankAtLeast (actionW (codeMat 98) (codeMat 266) (transposeW o120W)) 15 :=
    @quotientRankAtLeast_action (codeMat 98) (codeMat 266) hP hQ (transposeW o120W) 15 hT
  exact quotientRankAtLeast_mono step103o279s3_source_le_transport hAct

-- Source 4: compressed row 4, orbit 29, action, lb 15
def step103o279ActualSource4 : Submodule F2 Mat3 := spanCodes [160, 68, 16, 8, 2, 1]

private theorem step103o279_o279W_le_src4 : o279W ≤ spanCodes [160, 68, 16, 8, 2, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [160, 68, 16, 8, 2, 1] 10 (by decide)
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s4_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s4_source_le_transport :
    step103o279ActualSource4 ≤ actionW (codeMat 266) (codeMat 266) orbit29W := by
  apply step103o279_spanCodes_le_of_gens [160, 68, 16, 8, 2, 1]
    (actionW (codeMat 266) (codeMat 266) orbit29W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 68 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 68 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 68) = codeMat 160 := by
      unfold actionA
      rw [step103o279s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 68 * (codeMat 266 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 160 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 160) = codeMat 68 := by
      unfold actionA
      rw [step103o279s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 160 * (codeMat 266 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step103o279s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 2) = codeMat 8 := by
      unfold actionA
      rw [step103o279s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 266 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 8) = codeMat 2 := by
      unfold actionA
      rw [step103o279s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 266 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step103o279s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s4_qr :
    QuotientRankAtLeast step103o279ActualSource4 15 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 266) orbit29W) 15 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 266) hP hQ orbit29W 15 orbit29_lb15
  exact quotientRankAtLeast_mono step103o279s4_source_le_transport hAct

-- Source 5: compressed row 5, orbit 29, action, lb 15
def step103o279ActualSource5 : Submodule F2 Mat3 := spanCodes [164, 68, 16, 8, 2, 1]

private theorem step103o279_o279W_le_src5 : o279W ≤ spanCodes [164, 68, 16, 8, 2, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [164, 68, 16, 8, 2, 1] 10 (by decide)
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s5_QtInv :
    (codeMat 282 : Mat3).transpose⁻¹ = (codeMat 267 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 282 : Mat3).transpose * (codeMat 267 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s5_source_le_transport :
    step103o279ActualSource5 ≤ actionW (codeMat 266) (codeMat 282) orbit29W := by
  apply step103o279_spanCodes_le_of_gens [164, 68, 16, 8, 2, 1]
    (actionW (codeMat 266) (codeMat 282) orbit29W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 228 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 228 (by decide)
    have hact : actionA (codeMat 266) (codeMat 282) (codeMat 228) = codeMat 164 := by
      unfold actionA
      rw [step103o279s5_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 228 * (codeMat 267 : Mat3).transpose = codeMat 164
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 160 (by decide)
    have hact : actionA (codeMat 266) (codeMat 282) (codeMat 160) = codeMat 68 := by
      unfold actionA
      rw [step103o279s5_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 160 * (codeMat 267 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 3 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 3 (by decide)
    have hact : actionA (codeMat 266) (codeMat 282) (codeMat 3) = codeMat 16 := by
      unfold actionA
      rw [step103o279s5_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 3 * (codeMat 267 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 282) (codeMat 2) = codeMat 8 := by
      unfold actionA
      rw [step103o279s5_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 267 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 24 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 24 (by decide)
    have hact : actionA (codeMat 266) (codeMat 282) (codeMat 24) = codeMat 2 := by
      unfold actionA
      rw [step103o279s5_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 24 * (codeMat 267 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 282) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step103o279s5_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 267 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s5_qr :
    QuotientRankAtLeast step103o279ActualSource5 15 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 282 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 282) orbit29W) 15 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 282) hP hQ orbit29W 15 orbit29_lb15
  exact quotientRankAtLeast_mono step103o279s5_source_le_transport hAct

-- Source 6: compressed row 6, orbit 65, action, lb 15
def step103o279ActualSource6 : Submodule F2 Mat3 := spanCodes [290, 162, 68, 16, 10, 1]

private theorem step103o279_o279W_le_src6 : o279W ≤ spanCodes [290, 162, 68, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s6_QtInv :
    (codeMat 314 : Mat3).transpose⁻¹ = (codeMat 271 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 314 : Mat3).transpose * (codeMat 271 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s6_source_le_transport :
    step103o279ActualSource6 ≤ actionW (codeMat 267) (codeMat 314) o65W := by
  apply step103o279_spanCodes_le_of_gens [290, 162, 68, 16, 10, 1]
    (actionW (codeMat 267) (codeMat 314) o65W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 430 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 430 (by decide)
    have hact : actionA (codeMat 267) (codeMat 314) (codeMat 430) = codeMat 290 := by
      unfold actionA
      rw [step103o279s6_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 430 * (codeMat 271 : Mat3).transpose = codeMat 290
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 238 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 238 (by decide)
    have hact : actionA (codeMat 267) (codeMat 314) (codeMat 238) = codeMat 162 := by
      unfold actionA
      rw [step103o279s6_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 238 * (codeMat 271 : Mat3).transpose = codeMat 162
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 176 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 176 (by decide)
    have hact : actionA (codeMat 267) (codeMat 314) (codeMat 176) = codeMat 68 := by
      unfold actionA
      rw [step103o279s6_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 176 * (codeMat 271 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 27 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 27 (by decide)
    have hact : actionA (codeMat 267) (codeMat 314) (codeMat 27) = codeMat 16 := by
      unfold actionA
      rw [step103o279s6_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 27 * (codeMat 271 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 10 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 267) (codeMat 314) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step103o279s6_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 10 * (codeMat 271 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 267) (codeMat 314) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step103o279s6_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 16 * (codeMat 271 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s6_qr :
    QuotientRankAtLeast step103o279ActualSource6 15 := by
  have hP : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 314 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 267) (codeMat 314) o65W) 15 :=
    @quotientRankAtLeast_action (codeMat 267) (codeMat 314) hP hQ o65W 15 step99_orbit65_lb15_unconditional
  exact quotientRankAtLeast_mono step103o279s6_source_le_transport hAct

-- Source 7: compressed row 7, orbit 65, action, lb 15
def step103o279ActualSource7 : Submodule F2 Mat3 := spanCodes [288, 162, 68, 16, 10, 1]

private theorem step103o279_o279W_le_src7 : o279W ≤ spanCodes [288, 162, 68, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s7_QtInv :
    (codeMat 282 : Mat3).transpose⁻¹ = (codeMat 267 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 282 : Mat3).transpose * (codeMat 267 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s7_source_le_transport :
    step103o279ActualSource7 ≤ actionW (codeMat 331) (codeMat 282) o65W := by
  apply step103o279_spanCodes_le_of_gens [288, 162, 68, 16, 10, 1]
    (actionW (codeMat 331) (codeMat 282) o65W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 260 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 260 (by decide)
    have hact : actionA (codeMat 331) (codeMat 282) (codeMat 260) = codeMat 288 := by
      unfold actionA
      rw [step103o279s7_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 260 * (codeMat 267 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 228 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 228 (by decide)
    have hact : actionA (codeMat 331) (codeMat 282) (codeMat 228) = codeMat 162 := by
      unfold actionA
      rw [step103o279s7_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 228 * (codeMat 267 : Mat3).transpose = codeMat 162
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 176 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 176 (by decide)
    have hact : actionA (codeMat 331) (codeMat 282) (codeMat 176) = codeMat 68 := by
      unfold actionA
      rw [step103o279s7_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 176 * (codeMat 267 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 27 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 27 (by decide)
    have hact : actionA (codeMat 331) (codeMat 282) (codeMat 27) = codeMat 16 := by
      unfold actionA
      rw [step103o279s7_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 27 * (codeMat 267 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 10 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 331) (codeMat 282) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step103o279s7_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 10 * (codeMat 267 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 331) (codeMat 282) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step103o279s7_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 16 * (codeMat 267 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s7_qr :
    QuotientRankAtLeast step103o279ActualSource7 15 := by
  have hP : Invertible (codeMat 331 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 282 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 331) (codeMat 282) o65W) 15 :=
    @quotientRankAtLeast_action (codeMat 331) (codeMat 282) hP hQ o65W 15 step99_orbit65_lb15_unconditional
  exact quotientRankAtLeast_mono step103o279s7_source_le_transport hAct

-- Source 8: compressed row 8, orbit 65, action, lb 15
def step103o279ActualSource8 : Submodule F2 Mat3 := spanCodes [290, 160, 68, 16, 10, 1]

private theorem step103o279_o279W_le_src8 : o279W ≤ spanCodes [290, 160, 68, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s8_QtInv :
    (codeMat 298 : Mat3).transpose⁻¹ = (codeMat 270 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 298 : Mat3).transpose * (codeMat 270 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s8_source_le_transport :
    step103o279ActualSource8 ≤ actionW (codeMat 330) (codeMat 298) o65W := by
  apply step103o279_spanCodes_le_of_gens [290, 160, 68, 16, 10, 1]
    (actionW (codeMat 330) (codeMat 298) o65W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 446 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 446 (by decide)
    have hact : actionA (codeMat 330) (codeMat 298) (codeMat 446) = codeMat 290 := by
      unfold actionA
      rw [step103o279s8_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 446 * (codeMat 270 : Mat3).transpose = codeMat 290
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 78 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 78 (by decide)
    have hact : actionA (codeMat 330) (codeMat 298) (codeMat 78) = codeMat 160 := by
      unfold actionA
      rw [step103o279s8_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 78 * (codeMat 270 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 160 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 330) (codeMat 298) (codeMat 160) = codeMat 68 := by
      unfold actionA
      rw [step103o279s8_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 160 * (codeMat 270 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 330) (codeMat 298) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step103o279s8_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 1 * (codeMat 270 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 10 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 330) (codeMat 298) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step103o279s8_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 10 * (codeMat 270 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 330) (codeMat 298) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step103o279s8_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 16 * (codeMat 270 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s8_qr :
    QuotientRankAtLeast step103o279ActualSource8 15 := by
  have hP : Invertible (codeMat 330 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 298 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 330) (codeMat 298) o65W) 15 :=
    @quotientRankAtLeast_action (codeMat 330) (codeMat 298) hP hQ o65W 15 step99_orbit65_lb15_unconditional
  exact quotientRankAtLeast_mono step103o279s8_source_le_transport hAct

-- Source 9: compressed row 9, orbit 65, action, lb 15
def step103o279ActualSource9 : Submodule F2 Mat3 := spanCodes [292, 162, 68, 16, 10, 1]

private theorem step103o279_o279W_le_src9 : o279W ≤ spanCodes [292, 162, 68, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s9_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s9_source_le_transport :
    step103o279ActualSource9 ≤ actionW (codeMat 330) (codeMat 266) o65W := by
  apply step103o279_spanCodes_le_of_gens [292, 162, 68, 16, 10, 1]
    (actionW (codeMat 330) (codeMat 266) o65W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 260 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 260 (by decide)
    have hact : actionA (codeMat 330) (codeMat 266) (codeMat 260) = codeMat 292 := by
      unfold actionA
      rw [step103o279s9_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 260 * (codeMat 266 : Mat3).transpose = codeMat 292
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 68 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 330) (codeMat 266) (codeMat 68) = codeMat 162 := by
      unfold actionA
      rw [step103o279s9_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 68 * (codeMat 266 : Mat3).transpose = codeMat 162
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 176 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 176 (by decide)
    have hact : actionA (codeMat 330) (codeMat 266) (codeMat 176) = codeMat 68 := by
      unfold actionA
      rw [step103o279s9_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 176 * (codeMat 266 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 330) (codeMat 266) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step103o279s9_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 10 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 330) (codeMat 266) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step103o279s9_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 10 * (codeMat 266 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 330) (codeMat 266) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step103o279s9_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 16 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s9_qr :
    QuotientRankAtLeast step103o279ActualSource9 15 := by
  have hP : Invertible (codeMat 330 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 330) (codeMat 266) o65W) 15 :=
    @quotientRankAtLeast_action (codeMat 330) (codeMat 266) hP hQ o65W 15 step99_orbit65_lb15_unconditional
  exact quotientRankAtLeast_mono step103o279s9_source_le_transport hAct

-- Source 10: compressed row 10, orbit 11, action, lb 12
def step103o279ActualSource10 : Submodule F2 Mat3 := spanCodes [258, 130, 64, 16, 10, 4, 1]

private theorem step103o279_o279W_le_src10 : o279W ≤ spanCodes [258, 130, 64, 16, 10, 4, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 130, 64, 16, 10, 4, 1] 68 (by decide)
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s10_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s10_source_le_transport :
    step103o279ActualSource10 ≤ actionW (codeMat 141) (codeMat 273) orbit11W := by
  apply step103o279_spanCodes_le_of_gens [258, 130, 64, 16, 10, 4, 1]
    (actionW (codeMat 141) (codeMat 273) orbit11W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 52 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 52 (by decide)
    have hact : actionA (codeMat 141) (codeMat 273) (codeMat 52) = codeMat 258 := by
      unfold actionA
      rw [step103o279s10_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 52 * (codeMat 273 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 2 (by decide)
    have hact : actionA (codeMat 141) (codeMat 273) (codeMat 2) = codeMat 130 := by
      unfold actionA
      rw [step103o279s10_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 9 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 9 (by decide)
    have hact : actionA (codeMat 141) (codeMat 273) (codeMat 9) = codeMat 64 := by
      unfold actionA
      rw [step103o279s10_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 9 * (codeMat 273 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 128 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 128 (by decide)
    have hact : actionA (codeMat 141) (codeMat 273) (codeMat 128) = codeMat 16 := by
      unfold actionA
      rw [step103o279s10_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 128 * (codeMat 273 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 80 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 80 (by decide)
    have hact : actionA (codeMat 141) (codeMat 273) (codeMat 80) = codeMat 10 := by
      unfold actionA
      rw [step103o279s10_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 80 * (codeMat 273 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 32 (by decide)
    have hact : actionA (codeMat 141) (codeMat 273) (codeMat 32) = codeMat 4 := by
      unfold actionA
      rw [step103o279s10_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 32 * (codeMat 273 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 8 (by decide)
    have hact : actionA (codeMat 141) (codeMat 273) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step103o279s10_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 8 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s10_qr :
    QuotientRankAtLeast step103o279ActualSource10 12 := by
  have hP : Invertible (codeMat 141 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 141) (codeMat 273) orbit11W) 12 :=
    @quotientRankAtLeast_action (codeMat 141) (codeMat 273) hP hQ orbit11W 12 orbit11_lb12
  exact quotientRankAtLeast_mono step103o279s10_source_le_transport hAct

-- Source 11: compressed row 11, orbit 11, action, lb 12
def step103o279ActualSource11 : Submodule F2 Mat3 := spanCodes [258, 128, 64, 16, 10, 4, 1]

private theorem step103o279_o279W_le_src11 : o279W ≤ spanCodes [258, 128, 64, 16, 10, 4, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 128, 64, 16, 10, 4, 1] 68 (by decide)
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s11_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s11_source_le_transport :
    step103o279ActualSource11 ≤ actionW (codeMat 140) (codeMat 273) orbit11W := by
  apply step103o279_spanCodes_le_of_gens [258, 128, 64, 16, 10, 4, 1]
    (actionW (codeMat 140) (codeMat 273) orbit11W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 20 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 20 (by decide)
    have hact : actionA (codeMat 140) (codeMat 273) (codeMat 20) = codeMat 258 := by
      unfold actionA
      rw [step103o279s11_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 20 * (codeMat 273 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 2 (by decide)
    have hact : actionA (codeMat 140) (codeMat 273) (codeMat 2) = codeMat 128 := by
      unfold actionA
      rw [step103o279s11_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 1 (by decide)
    have hact : actionA (codeMat 140) (codeMat 273) (codeMat 1) = codeMat 64 := by
      unfold actionA
      rw [step103o279s11_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 128 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 128 (by decide)
    have hact : actionA (codeMat 140) (codeMat 273) (codeMat 128) = codeMat 16 := by
      unfold actionA
      rw [step103o279s11_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 128 * (codeMat 273 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 80 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 80 (by decide)
    have hact : actionA (codeMat 140) (codeMat 273) (codeMat 80) = codeMat 10 := by
      unfold actionA
      rw [step103o279s11_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 80 * (codeMat 273 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 32 (by decide)
    have hact : actionA (codeMat 140) (codeMat 273) (codeMat 32) = codeMat 4 := by
      unfold actionA
      rw [step103o279s11_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 32 * (codeMat 273 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 8 (by decide)
    have hact : actionA (codeMat 140) (codeMat 273) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step103o279s11_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 8 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s11_qr :
    QuotientRankAtLeast step103o279ActualSource11 12 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 273) orbit11W) 12 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 273) hP hQ orbit11W 12 orbit11_lb12
  exact quotientRankAtLeast_mono step103o279s11_source_le_transport hAct

-- Source 12: compressed row 12, orbit 10, action, lb 12
def step103o279ActualSource12 : Submodule F2 Mat3 := spanCodes [256, 132, 68, 36, 16, 10, 1]

private theorem step103o279_o279W_le_src12 : o279W ≤ spanCodes [256, 132, 68, 36, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s12_QtInv :
    (codeMat 212 : Mat3).transpose⁻¹ = (codeMat 86 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 212 : Mat3).transpose * (codeMat 86 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s12_source_le_transport :
    step103o279ActualSource12 ≤ actionW (codeMat 92) (codeMat 212) orbit10W := by
  apply step103o279_spanCodes_le_of_gens [256, 132, 68, 36, 16, 10, 1]
    (actionW (codeMat 92) (codeMat 212) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 92) (codeMat 212) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step103o279s12_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 1 * (codeMat 86 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 70 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 70 (by decide)
    have hact : actionA (codeMat 92) (codeMat 212) (codeMat 70) = codeMat 132 := by
      unfold actionA
      rw [step103o279s12_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 70 * (codeMat 86 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 92) (codeMat 212) (codeMat 68) = codeMat 68 := by
      unfold actionA
      rw [step103o279s12_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 68 * (codeMat 86 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 92) (codeMat 212) (codeMat 8) = codeMat 36 := by
      unfold actionA
      rw [step103o279s12_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 8 * (codeMat 86 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 432 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 432 (by decide)
    have hact : actionA (codeMat 92) (codeMat 212) (codeMat 432) = codeMat 16 := by
      unfold actionA
      rw [step103o279s12_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 432 * (codeMat 86 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 92) (codeMat 212) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step103o279s12_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 160 * (codeMat 86 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 92) (codeMat 212) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step103o279s12_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 256 * (codeMat 86 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s12_qr :
    QuotientRankAtLeast step103o279ActualSource12 12 := by
  have hP : Invertible (codeMat 92 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 212 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 92) (codeMat 212) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 92) (codeMat 212) hP hQ orbit10W 12 orbit10_lb12
  exact quotientRankAtLeast_mono step103o279s12_source_le_transport hAct

-- Source 13: compressed row 13, orbit 14, action, lb 12
def step103o279ActualSource13 : Submodule F2 Mat3 := spanCodes [260, 128, 68, 38, 16, 10, 1]

private theorem step103o279_o279W_le_src13 : o279W ≤ spanCodes [260, 128, 68, 38, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s13_QtInv :
    (codeMat 359 : Mat3).transpose⁻¹ = (codeMat 174 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 359 : Mat3).transpose * (codeMat 174 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s13_source_le_transport :
    step103o279ActualSource13 ≤ actionW (codeMat 212) (codeMat 359) orbit14W := by
  apply step103o279_spanCodes_le_of_gens [260, 128, 68, 38, 16, 10, 1]
    (actionW (codeMat 212) (codeMat 359) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 511 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 511 (by decide)
    have hact : actionA (codeMat 212) (codeMat 359) (codeMat 511) = codeMat 260 := by
      unfold actionA
      rw [step103o279s13_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 511 * (codeMat 174 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 212) (codeMat 359) (codeMat 1) = codeMat 128 := by
      unfold actionA
      rw [step103o279s13_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 1 * (codeMat 174 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 509 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 509 (by decide)
    have hact : actionA (codeMat 212) (codeMat 359) (codeMat 509) = codeMat 68 := by
      unfold actionA
      rw [step103o279s13_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 509 * (codeMat 174 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 392 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 392 (by decide)
    have hact : actionA (codeMat 212) (codeMat 359) (codeMat 392) = codeMat 38 := by
      unfold actionA
      rw [step103o279s13_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 392 * (codeMat 174 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 212) (codeMat 359) (codeMat 8) = codeMat 16 := by
      unfold actionA
      rw [step103o279s13_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 8 * (codeMat 174 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 212) (codeMat 359) (codeMat 96) = codeMat 10 := by
      unfold actionA
      rw [step103o279s13_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 96 * (codeMat 174 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 212) (codeMat 359) (codeMat 360) = codeMat 1 := by
      unfold actionA
      rw [step103o279s13_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 360 * (codeMat 174 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s13_qr :
    QuotientRankAtLeast step103o279ActualSource13 12 := by
  have hP : Invertible (codeMat 212 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 359 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 212) (codeMat 359) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 212) (codeMat 359) hP hQ orbit14W 12 orbit14_lb12
  exact quotientRankAtLeast_mono step103o279s13_source_le_transport hAct

-- Source 14: compressed row 14, orbit 14, action, lb 12
def step103o279ActualSource14 : Submodule F2 Mat3 := spanCodes [260, 130, 68, 36, 16, 10, 1]

private theorem step103o279_o279W_le_src14 : o279W ≤ spanCodes [260, 130, 68, 36, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s14_QtInv :
    (codeMat 99 : Mat3).transpose⁻¹ = (codeMat 172 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 99 : Mat3).transpose * (codeMat 172 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s14_source_le_transport :
    step103o279ActualSource14 ≤ actionW (codeMat 213) (codeMat 99) orbit14W := by
  apply step103o279_spanCodes_le_of_gens [260, 130, 68, 36, 16, 10, 1]
    (actionW (codeMat 213) (codeMat 99) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 213) (codeMat 99) (codeMat 2) = codeMat 260 := by
      unfold actionA
      rw [step103o279s14_QtInv]
      show (codeMat 213 : Mat3).transpose * codeMat 2 * (codeMat 172 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 213) (codeMat 99) (codeMat 1) = codeMat 130 := by
      unfold actionA
      rw [step103o279s14_QtInv]
      show (codeMat 213 : Mat3).transpose * codeMat 1 * (codeMat 172 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 509 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 509 (by decide)
    have hact : actionA (codeMat 213) (codeMat 99) (codeMat 509) = codeMat 68 := by
      unfold actionA
      rw [step103o279s14_QtInv]
      show (codeMat 213 : Mat3).transpose * codeMat 509 * (codeMat 172 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 213) (codeMat 99) (codeMat 128) = codeMat 36 := by
      unfold actionA
      rw [step103o279s14_QtInv]
      show (codeMat 213 : Mat3).transpose * codeMat 128 * (codeMat 172 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 213) (codeMat 99) (codeMat 8) = codeMat 16 := by
      unfold actionA
      rw [step103o279s14_QtInv]
      show (codeMat 213 : Mat3).transpose * codeMat 8 * (codeMat 172 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 213) (codeMat 99) (codeMat 96) = codeMat 10 := by
      unfold actionA
      rw [step103o279s14_QtInv]
      show (codeMat 213 : Mat3).transpose * codeMat 96 * (codeMat 172 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 213) (codeMat 99) (codeMat 360) = codeMat 1 := by
      unfold actionA
      rw [step103o279s14_QtInv]
      show (codeMat 213 : Mat3).transpose * codeMat 360 * (codeMat 172 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s14_qr :
    QuotientRankAtLeast step103o279ActualSource14 12 := by
  have hP : Invertible (codeMat 213 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 99 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 213) (codeMat 99) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 213) (codeMat 99) hP hQ orbit14W 12 orbit14_lb12
  exact quotientRankAtLeast_mono step103o279s14_source_le_transport hAct

-- Source 15: compressed row 15, orbit 11, action, lb 12
def step103o279ActualSource15 : Submodule F2 Mat3 := spanCodes [290, 128, 66, 16, 10, 6, 1]

private theorem step103o279_o279W_le_src15 : o279W ≤ spanCodes [290, 128, 66, 16, 10, 6, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [290, 128, 66, 16, 10, 6, 1] 68 (by decide)
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s15_QtInv :
    (codeMat 305 : Mat3).transpose⁻¹ = (codeMat 305 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 305 : Mat3).transpose * (codeMat 305 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s15_source_le_transport :
    step103o279ActualSource15 ≤ actionW (codeMat 142) (codeMat 305) orbit11W := by
  apply step103o279_spanCodes_le_of_gens [290, 128, 66, 16, 10, 6, 1]
    (actionW (codeMat 142) (codeMat 305) orbit11W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 22 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 22 (by decide)
    have hact : actionA (codeMat 142) (codeMat 305) (codeMat 22) = codeMat 290 := by
      unfold actionA
      rw [step103o279s15_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 22 * (codeMat 305 : Mat3).transpose = codeMat 290
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 130 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 130 (by decide)
    have hact : actionA (codeMat 142) (codeMat 305) (codeMat 130) = codeMat 128 := by
      unfold actionA
      rw [step103o279s15_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 130 * (codeMat 305 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 81 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 81 (by decide)
    have hact : actionA (codeMat 142) (codeMat 305) (codeMat 81) = codeMat 66 := by
      unfold actionA
      rw [step103o279s15_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 81 * (codeMat 305 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 128 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 128 (by decide)
    have hact : actionA (codeMat 142) (codeMat 305) (codeMat 128) = codeMat 16 := by
      unfold actionA
      rw [step103o279s15_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 128 * (codeMat 305 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 80 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 80 (by decide)
    have hact : actionA (codeMat 142) (codeMat 305) (codeMat 80) = codeMat 10 := by
      unfold actionA
      rw [step103o279s15_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 80 * (codeMat 305 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 32 (by decide)
    have hact : actionA (codeMat 142) (codeMat 305) (codeMat 32) = codeMat 6 := by
      unfold actionA
      rw [step103o279s15_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 32 * (codeMat 305 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 8 (by decide)
    have hact : actionA (codeMat 142) (codeMat 305) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step103o279s15_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 8 * (codeMat 305 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s15_qr :
    QuotientRankAtLeast step103o279ActualSource15 12 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 305) orbit11W) 12 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 305) hP hQ orbit11W 12 orbit11_lb12
  exact quotientRankAtLeast_mono step103o279s15_source_le_transport hAct

-- Source 16: compressed row 16, orbit 10, action, lb 12
def step103o279ActualSource16 : Submodule F2 Mat3 := spanCodes [260, 132, 68, 38, 16, 10, 1]

private theorem step103o279_o279W_le_src16 : o279W ≤ spanCodes [260, 132, 68, 38, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s16_QtInv :
    (codeMat 468 : Mat3).transpose⁻¹ = (codeMat 87 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 468 : Mat3).transpose * (codeMat 87 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s16_source_le_transport :
    step103o279ActualSource16 ≤ actionW (codeMat 92) (codeMat 468) orbit10W := by
  apply step103o279_spanCodes_le_of_gens [260, 132, 68, 38, 16, 10, 1]
    (actionW (codeMat 92) (codeMat 468) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 325 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 325 (by decide)
    have hact : actionA (codeMat 92) (codeMat 468) (codeMat 325) = codeMat 260 := by
      unfold actionA
      rw [step103o279s16_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 325 * (codeMat 87 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 326 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 326 (by decide)
    have hact : actionA (codeMat 92) (codeMat 468) (codeMat 326) = codeMat 132 := by
      unfold actionA
      rw [step103o279s16_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 326 * (codeMat 87 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 324 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 324 (by decide)
    have hact : actionA (codeMat 92) (codeMat 468) (codeMat 324) = codeMat 68 := by
      unfold actionA
      rw [step103o279s16_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 324 * (codeMat 87 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 424 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 424 (by decide)
    have hact : actionA (codeMat 92) (codeMat 468) (codeMat 424) = codeMat 38 := by
      unfold actionA
      rw [step103o279s16_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 424 * (codeMat 87 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 432 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 432 (by decide)
    have hact : actionA (codeMat 92) (codeMat 468) (codeMat 432) = codeMat 16 := by
      unfold actionA
      rw [step103o279s16_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 432 * (codeMat 87 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 92) (codeMat 468) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step103o279s16_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 160 * (codeMat 87 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 92) (codeMat 468) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step103o279s16_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 256 * (codeMat 87 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s16_qr :
    QuotientRankAtLeast step103o279ActualSource16 12 := by
  have hP : Invertible (codeMat 92 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 468 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 92) (codeMat 468) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 92) (codeMat 468) hP hQ orbit10W 12 orbit10_lb12
  exact quotientRankAtLeast_mono step103o279s16_source_le_transport hAct

-- Source 17: compressed row 17, orbit 10, action, lb 12
def step103o279ActualSource17 : Submodule F2 Mat3 := spanCodes [260, 134, 68, 36, 16, 10, 1]

private theorem step103o279_o279W_le_src17 : o279W ≤ spanCodes [260, 134, 68, 36, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s17_QtInv :
    (codeMat 212 : Mat3).transpose⁻¹ = (codeMat 86 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 212 : Mat3).transpose * (codeMat 86 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s17_source_le_transport :
    step103o279ActualSource17 ≤ actionW (codeMat 93) (codeMat 212) orbit10W := by
  apply step103o279_spanCodes_le_of_gens [260, 134, 68, 36, 16, 10, 1]
    (actionW (codeMat 93) (codeMat 212) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 93) (codeMat 212) (codeMat 1) = codeMat 260 := by
      unfold actionA
      rw [step103o279s17_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 1 * (codeMat 86 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 70 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 70 (by decide)
    have hact : actionA (codeMat 93) (codeMat 212) (codeMat 70) = codeMat 134 := by
      unfold actionA
      rw [step103o279s17_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 70 * (codeMat 86 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 324 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 324 (by decide)
    have hact : actionA (codeMat 93) (codeMat 212) (codeMat 324) = codeMat 68 := by
      unfold actionA
      rw [step103o279s17_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 324 * (codeMat 86 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 93) (codeMat 212) (codeMat 8) = codeMat 36 := by
      unfold actionA
      rw [step103o279s17_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 8 * (codeMat 86 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 432 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 432 (by decide)
    have hact : actionA (codeMat 93) (codeMat 212) (codeMat 432) = codeMat 16 := by
      unfold actionA
      rw [step103o279s17_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 432 * (codeMat 86 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 93) (codeMat 212) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step103o279s17_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 160 * (codeMat 86 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 93) (codeMat 212) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step103o279s17_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 256 * (codeMat 86 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s17_qr :
    QuotientRankAtLeast step103o279ActualSource17 12 := by
  have hP : Invertible (codeMat 93 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 212 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 93) (codeMat 212) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 93) (codeMat 212) hP hQ orbit10W 12 orbit10_lb12
  exact quotientRankAtLeast_mono step103o279s17_source_le_transport hAct

-- Source 18: compressed row 18, orbit 10, action, lb 12
def step103o279ActualSource18 : Submodule F2 Mat3 := spanCodes [258, 162, 66, 16, 10, 6, 1]

private theorem step103o279_o279W_le_src18 : o279W ≤ spanCodes [258, 162, 66, 16, 10, 6, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 162, 66, 16, 10, 6, 1] 68 (by decide)
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s18_QtInv :
    (codeMat 428 : Mat3).transpose⁻¹ = (codeMat 107 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 428 : Mat3).transpose * (codeMat 107 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s18_source_le_transport :
    step103o279ActualSource18 ≤ actionW (codeMat 142) (codeMat 428) orbit10W := by
  apply step103o279_spanCodes_le_of_gens [258, 162, 66, 16, 10, 6, 1]
    (actionW (codeMat 142) (codeMat 428) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 487 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 487 (by decide)
    have hact : actionA (codeMat 142) (codeMat 428) (codeMat 487) = codeMat 258 := by
      unfold actionA
      rw [step103o279s18_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 487 * (codeMat 107 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 228 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 228 (by decide)
    have hact : actionA (codeMat 142) (codeMat 428) (codeMat 228) = codeMat 162 := by
      unfold actionA
      rw [step103o279s18_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 228 * (codeMat 107 : Mat3).transpose = codeMat 162
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 162 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 162 (by decide)
    have hact : actionA (codeMat 142) (codeMat 428) (codeMat 162) = codeMat 66 := by
      unfold actionA
      rw [step103o279s18_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 162 * (codeMat 107 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 142) (codeMat 428) (codeMat 256) = codeMat 16 := by
      unfold actionA
      rw [step103o279s18_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 256 * (codeMat 107 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 142) (codeMat 428) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step103o279s18_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 160 * (codeMat 107 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 24 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide)
    have hact : actionA (codeMat 142) (codeMat 428) (codeMat 24) = codeMat 6 := by
      unfold actionA
      rw [step103o279s18_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 24 * (codeMat 107 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 142) (codeMat 428) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step103o279s18_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 16 * (codeMat 107 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s18_qr :
    QuotientRankAtLeast step103o279ActualSource18 12 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 428 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 428) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 428) hP hQ orbit10W 12 orbit10_lb12
  exact quotientRankAtLeast_mono step103o279s18_source_le_transport hAct

-- Source 19: compressed row 19, orbit 10, action, lb 12
def step103o279ActualSource19 : Submodule F2 Mat3 := spanCodes [256, 160, 66, 16, 10, 6, 1]

private theorem step103o279_o279W_le_src19 : o279W ≤ spanCodes [256, 160, 66, 16, 10, 6, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 16, 10, 6, 1] 68 (by decide)
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s19_QtInv :
    (codeMat 396 : Mat3).transpose⁻¹ = (codeMat 106 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 396 : Mat3).transpose * (codeMat 106 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s19_source_le_transport :
    step103o279ActualSource19 ≤ actionW (codeMat 142) (codeMat 396) orbit10W := by
  apply step103o279_spanCodes_le_of_gens [256, 160, 66, 16, 10, 6, 1]
    (actionW (codeMat 142) (codeMat 396) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 325 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 325 (by decide)
    have hact : actionA (codeMat 142) (codeMat 396) (codeMat 325) = codeMat 256 := by
      unfold actionA
      rw [step103o279s19_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 325 * (codeMat 106 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 68 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 142) (codeMat 396) (codeMat 68) = codeMat 160 := by
      unfold actionA
      rw [step103o279s19_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 68 * (codeMat 106 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 162 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 162 (by decide)
    have hact : actionA (codeMat 142) (codeMat 396) (codeMat 162) = codeMat 66 := by
      unfold actionA
      rw [step103o279s19_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 162 * (codeMat 106 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 142) (codeMat 396) (codeMat 256) = codeMat 16 := by
      unfold actionA
      rw [step103o279s19_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 256 * (codeMat 106 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 142) (codeMat 396) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step103o279s19_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 160 * (codeMat 106 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 142) (codeMat 396) (codeMat 8) = codeMat 6 := by
      unfold actionA
      rw [step103o279s19_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 8 * (codeMat 106 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 142) (codeMat 396) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step103o279s19_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 16 * (codeMat 106 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s19_qr :
    QuotientRankAtLeast step103o279ActualSource19 12 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 396 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 396) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 396) hP hQ orbit10W 12 orbit10_lb12
  exact quotientRankAtLeast_mono step103o279s19_source_le_transport hAct

-- Source 20: compressed row 20, orbit 10, action, lb 12
def step103o279ActualSource20 : Submodule F2 Mat3 := spanCodes [256, 162, 64, 16, 10, 4, 1]

private theorem step103o279_o279W_le_src20 : o279W ≤ spanCodes [256, 162, 64, 16, 10, 4, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 162, 64, 16, 10, 4, 1] 68 (by decide)
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s20_QtInv :
    (codeMat 172 : Mat3).transpose⁻¹ = (codeMat 99 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 172 : Mat3).transpose * (codeMat 99 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s20_source_le_transport :
    step103o279ActualSource20 ≤ actionW (codeMat 140) (codeMat 172) orbit10W := by
  apply step103o279_spanCodes_le_of_gens [256, 162, 64, 16, 10, 4, 1]
    (actionW (codeMat 140) (codeMat 172) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 3 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 3 (by decide)
    have hact : actionA (codeMat 140) (codeMat 172) (codeMat 3) = codeMat 256 := by
      unfold actionA
      rw [step103o279s20_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 3 * (codeMat 99 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 228 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 228 (by decide)
    have hact : actionA (codeMat 140) (codeMat 172) (codeMat 228) = codeMat 162 := by
      unfold actionA
      rw [step103o279s20_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 228 * (codeMat 99 : Mat3).transpose = codeMat 162
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 140) (codeMat 172) (codeMat 2) = codeMat 64 := by
      unfold actionA
      rw [step103o279s20_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 2 * (codeMat 99 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 140) (codeMat 172) (codeMat 256) = codeMat 16 := by
      unfold actionA
      rw [step103o279s20_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 256 * (codeMat 99 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 140) (codeMat 172) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step103o279s20_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 160 * (codeMat 99 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 24 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide)
    have hact : actionA (codeMat 140) (codeMat 172) (codeMat 24) = codeMat 4 := by
      unfold actionA
      rw [step103o279s20_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 24 * (codeMat 99 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 140) (codeMat 172) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step103o279s20_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 16 * (codeMat 99 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s20_qr :
    QuotientRankAtLeast step103o279ActualSource20 12 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 172 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 172) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 172) hP hQ orbit10W 12 orbit10_lb12
  exact quotientRankAtLeast_mono step103o279s20_source_le_transport hAct

-- Source 21: compressed row 21, orbit 150, action, lb 16
def step103o279ActualSource21 : Submodule F2 Mat3 := spanCodes [258, 68, 16, 10, 1]

private theorem step103o279_o279W_le_src21 : o279W ≤ spanCodes [258, 68, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s21_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s21_source_le_transport :
    step103o279ActualSource21 ≤ actionW (codeMat 273) (codeMat 273) o150W := by
  apply step103o279_spanCodes_le_of_gens [258, 68, 16, 10, 1]
    (actionW (codeMat 273) (codeMat 273) o150W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 258 ∈ o150W :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 16, 10, 1] 258 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 258) = codeMat 258 := by
      unfold actionA
      rw [step103o279s21_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 258 * (codeMat 273 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 68 ∈ o150W :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 16, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 68) = codeMat 68 := by
      unfold actionA
      rw [step103o279s21_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 68 * (codeMat 273 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 16 ∈ o150W :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 16) = codeMat 16 := by
      unfold actionA
      rw [step103o279s21_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 16 * (codeMat 273 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 10 ∈ o150W :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 16, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step103o279s21_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 10 * (codeMat 273 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o150W :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step103o279s21_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s21_qr :
    QuotientRankAtLeast step103o279ActualSource21 16 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 273) o150W) 16 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 273) hP hQ o150W 16 step99_orbit150_lb16_unconditional
  exact quotientRankAtLeast_mono step103o279s21_source_le_transport hAct

-- Source 22: compressed row 22, orbit 150, action, lb 16
def step103o279ActualSource22 : Submodule F2 Mat3 := spanCodes [418, 68, 16, 10, 1]

private theorem step103o279_o279W_le_src22 : o279W ≤ spanCodes [418, 68, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s22_QtInv :
    (codeMat 305 : Mat3).transpose⁻¹ = (codeMat 305 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 305 : Mat3).transpose * (codeMat 305 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s22_source_le_transport :
    step103o279ActualSource22 ≤ actionW (codeMat 401) (codeMat 305) o150W := by
  apply step103o279_spanCodes_le_of_gens [418, 68, 16, 10, 1]
    (actionW (codeMat 401) (codeMat 305) o150W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 274 ∈ o150W :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 16, 10, 1] 274 (by decide)
    have hact : actionA (codeMat 401) (codeMat 305) (codeMat 274) = codeMat 418 := by
      unfold actionA
      rw [step103o279s22_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 274 * (codeMat 305 : Mat3).transpose = codeMat 418
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 78 ∈ o150W :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 16, 10, 1] 78 (by decide)
    have hact : actionA (codeMat 401) (codeMat 305) (codeMat 78) = codeMat 68 := by
      unfold actionA
      rw [step103o279s22_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 78 * (codeMat 305 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 16 ∈ o150W :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 401) (codeMat 305) (codeMat 16) = codeMat 16 := by
      unfold actionA
      rw [step103o279s22_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 16 * (codeMat 305 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 10 ∈ o150W :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 16, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 401) (codeMat 305) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step103o279s22_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 10 * (codeMat 305 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o150W :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 401) (codeMat 305) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step103o279s22_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 1 * (codeMat 305 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s22_qr :
    QuotientRankAtLeast step103o279ActualSource22 16 := by
  have hP : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 401) (codeMat 305) o150W) 16 :=
    @quotientRankAtLeast_action (codeMat 401) (codeMat 305) hP hQ o150W 16 step99_orbit150_lb16_unconditional
  exact quotientRankAtLeast_mono step103o279s22_source_le_transport hAct

-- Source 23: compressed row 23, orbit 65, action, lb 15
def step103o279ActualSource23 : Submodule F2 Mat3 := spanCodes [288, 160, 68, 16, 10, 1]

private theorem step103o279_o279W_le_src23 : o279W ≤ spanCodes [288, 160, 68, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s23_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s23_source_le_transport :
    step103o279ActualSource23 ≤ actionW (codeMat 266) (codeMat 266) o65W := by
  apply step103o279_spanCodes_le_of_gens [288, 160, 68, 16, 10, 1]
    (actionW (codeMat 266) (codeMat 266) o65W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 260 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 260 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 260) = codeMat 288 := by
      unfold actionA
      rw [step103o279s23_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 260 * (codeMat 266 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 68 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 68) = codeMat 160 := by
      unfold actionA
      rw [step103o279s23_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 68 * (codeMat 266 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 160 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 160) = codeMat 68 := by
      unfold actionA
      rw [step103o279s23_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 160 * (codeMat 266 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step103o279s23_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 10 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step103o279s23_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 10 * (codeMat 266 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step103o279s23_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s23_qr :
    QuotientRankAtLeast step103o279ActualSource23 15 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 266) o65W) 15 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 266) hP hQ o65W 15 step99_orbit65_lb15_unconditional
  exact quotientRankAtLeast_mono step103o279s23_source_le_transport hAct

-- Source 24: compressed row 24, orbit 11, action, lb 12
def step103o279ActualSource24 : Submodule F2 Mat3 := spanCodes [258, 64, 32, 16, 10, 4, 1]

private theorem step103o279_o279W_le_src24 : o279W ≤ spanCodes [258, 64, 32, 16, 10, 4, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 64, 32, 16, 10, 4, 1] 68 (by decide)
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s24_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s24_source_le_transport :
    step103o279ActualSource24 ≤ actionW (codeMat 273) (codeMat 140) orbit11W := by
  apply step103o279_spanCodes_le_of_gens [258, 64, 32, 16, 10, 4, 1]
    (actionW (codeMat 273) (codeMat 140) orbit11W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 68 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 68 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 68) = codeMat 258 := by
      unfold actionA
      rw [step103o279s24_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 68 * (codeMat 98 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 128 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 128 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 128) = codeMat 64 := by
      unfold actionA
      rw [step103o279s24_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 128 * (codeMat 98 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step103o279s24_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 32 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 32 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 32) = codeMat 16 := by
      unfold actionA
      rw [step103o279s24_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 32 * (codeMat 98 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 20 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 20 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 20) = codeMat 10 := by
      unfold actionA
      rw [step103o279s24_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 20 * (codeMat 98 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 1) = codeMat 4 := by
      unfold actionA
      rw [step103o279s24_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step103o279s24_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s24_qr :
    QuotientRankAtLeast step103o279ActualSource24 12 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 140) orbit11W) 12 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 140) hP hQ orbit11W 12 orbit11_lb12
  exact quotientRankAtLeast_mono step103o279s24_source_le_transport hAct

-- Source 25: compressed row 25, orbit 10, action, lb 12
def step103o279ActualSource25 : Submodule F2 Mat3 := spanCodes [256, 134, 68, 38, 16, 10, 1]

private theorem step103o279_o279W_le_src25 : o279W ≤ spanCodes [256, 134, 68, 38, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s25_QtInv :
    (codeMat 468 : Mat3).transpose⁻¹ = (codeMat 87 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 468 : Mat3).transpose * (codeMat 87 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s25_source_le_transport :
    step103o279ActualSource25 ≤ actionW (codeMat 93) (codeMat 468) orbit10W := by
  apply step103o279_spanCodes_le_of_gens [256, 134, 68, 38, 16, 10, 1]
    (actionW (codeMat 93) (codeMat 468) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 325 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 325 (by decide)
    have hact : actionA (codeMat 93) (codeMat 468) (codeMat 325) = codeMat 256 := by
      unfold actionA
      rw [step103o279s25_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 325 * (codeMat 87 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 326 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 326 (by decide)
    have hact : actionA (codeMat 93) (codeMat 468) (codeMat 326) = codeMat 134 := by
      unfold actionA
      rw [step103o279s25_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 326 * (codeMat 87 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 93) (codeMat 468) (codeMat 68) = codeMat 68 := by
      unfold actionA
      rw [step103o279s25_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 68 * (codeMat 87 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 424 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 424 (by decide)
    have hact : actionA (codeMat 93) (codeMat 468) (codeMat 424) = codeMat 38 := by
      unfold actionA
      rw [step103o279s25_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 424 * (codeMat 87 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 432 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 432 (by decide)
    have hact : actionA (codeMat 93) (codeMat 468) (codeMat 432) = codeMat 16 := by
      unfold actionA
      rw [step103o279s25_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 432 * (codeMat 87 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 93) (codeMat 468) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step103o279s25_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 160 * (codeMat 87 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 93) (codeMat 468) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step103o279s25_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 256 * (codeMat 87 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s25_qr :
    QuotientRankAtLeast step103o279ActualSource25 12 := by
  have hP : Invertible (codeMat 93 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 468 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 93) (codeMat 468) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 93) (codeMat 468) hP hQ orbit10W 12 orbit10_lb12
  exact quotientRankAtLeast_mono step103o279s25_source_le_transport hAct

-- Source 26: compressed row 26, orbit 10, action, lb 12
def step103o279ActualSource26 : Submodule F2 Mat3 := spanCodes [256, 160, 64, 16, 10, 4, 1]

private theorem step103o279_o279W_le_src26 : o279W ≤ spanCodes [256, 160, 64, 16, 10, 4, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 10, 4, 1] 68 (by decide)
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s26_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s26_source_le_transport :
    step103o279ActualSource26 ≤ actionW (codeMat 140) (codeMat 140) orbit10W := by
  apply step103o279_spanCodes_le_of_gens [256, 160, 64, 16, 10, 4, 1]
    (actionW (codeMat 140) (codeMat 140) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 140) (codeMat 140) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step103o279s26_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 68 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 140) (codeMat 140) (codeMat 68) = codeMat 160 := by
      unfold actionA
      rw [step103o279s26_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 68 * (codeMat 98 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 140) (codeMat 140) (codeMat 2) = codeMat 64 := by
      unfold actionA
      rw [step103o279s26_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 2 * (codeMat 98 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 140) (codeMat 140) (codeMat 256) = codeMat 16 := by
      unfold actionA
      rw [step103o279s26_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 256 * (codeMat 98 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 140) (codeMat 140) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step103o279s26_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 160 * (codeMat 98 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 140) (codeMat 140) (codeMat 8) = codeMat 4 := by
      unfold actionA
      rw [step103o279s26_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 140) (codeMat 140) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step103o279s26_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 16 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s26_qr :
    QuotientRankAtLeast step103o279ActualSource26 12 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 140) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 140) hP hQ orbit10W 12 orbit10_lb12
  exact quotientRankAtLeast_mono step103o279s26_source_le_transport hAct

-- Source 27: compressed row 27, orbit 11, action, lb 12
def step103o279ActualSource27 : Submodule F2 Mat3 := spanCodes [288, 130, 66, 16, 10, 6, 1]

private theorem step103o279_o279W_le_src27 : o279W ≤ spanCodes [288, 130, 66, 16, 10, 6, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 130, 66, 16, 10, 6, 1] 68 (by decide)
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s27_QtInv :
    (codeMat 305 : Mat3).transpose⁻¹ = (codeMat 305 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 305 : Mat3).transpose * (codeMat 305 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s27_source_le_transport :
    step103o279ActualSource27 ≤ actionW (codeMat 143) (codeMat 305) orbit11W := by
  apply step103o279_spanCodes_le_of_gens [288, 130, 66, 16, 10, 6, 1]
    (actionW (codeMat 143) (codeMat 305) orbit11W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 54 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 54 (by decide)
    have hact : actionA (codeMat 143) (codeMat 305) (codeMat 54) = codeMat 288 := by
      unfold actionA
      rw [step103o279s27_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 54 * (codeMat 305 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 130 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 130 (by decide)
    have hact : actionA (codeMat 143) (codeMat 305) (codeMat 130) = codeMat 130 := by
      unfold actionA
      rw [step103o279s27_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 130 * (codeMat 305 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 89 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 89 (by decide)
    have hact : actionA (codeMat 143) (codeMat 305) (codeMat 89) = codeMat 66 := by
      unfold actionA
      rw [step103o279s27_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 89 * (codeMat 305 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 128 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 128 (by decide)
    have hact : actionA (codeMat 143) (codeMat 305) (codeMat 128) = codeMat 16 := by
      unfold actionA
      rw [step103o279s27_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 128 * (codeMat 305 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 80 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 80 (by decide)
    have hact : actionA (codeMat 143) (codeMat 305) (codeMat 80) = codeMat 10 := by
      unfold actionA
      rw [step103o279s27_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 80 * (codeMat 305 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 32 (by decide)
    have hact : actionA (codeMat 143) (codeMat 305) (codeMat 32) = codeMat 6 := by
      unfold actionA
      rw [step103o279s27_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 32 * (codeMat 305 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 8 (by decide)
    have hact : actionA (codeMat 143) (codeMat 305) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step103o279s27_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 8 * (codeMat 305 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s27_qr :
    QuotientRankAtLeast step103o279ActualSource27 12 := by
  have hP : Invertible (codeMat 143 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 143) (codeMat 305) orbit11W) 12 :=
    @quotientRankAtLeast_action (codeMat 143) (codeMat 305) hP hQ orbit11W 12 orbit11_lb12
  exact quotientRankAtLeast_mono step103o279s27_source_le_transport hAct

-- Source 28: compressed row 28, orbit 11, action, lb 12
def step103o279ActualSource28 : Submodule F2 Mat3 := spanCodes [386, 66, 32, 16, 10, 6, 1]

private theorem step103o279_o279W_le_src28 : o279W ≤ spanCodes [386, 66, 32, 16, 10, 6, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [386, 66, 32, 16, 10, 6, 1] 68 (by decide)
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s28_QtInv :
    (codeMat 395 : Mat3).transpose⁻¹ = (codeMat 474 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 395 : Mat3).transpose * (codeMat 474 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s28_source_le_transport :
    step103o279ActualSource28 ≤ actionW (codeMat 273) (codeMat 395) orbit11W := by
  apply step103o279_spanCodes_le_of_gens [386, 66, 32, 16, 10, 6, 1]
    (actionW (codeMat 273) (codeMat 395) orbit11W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 69 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 69 (by decide)
    have hact : actionA (codeMat 273) (codeMat 395) (codeMat 69) = codeMat 386 := by
      unfold actionA
      rw [step103o279s28_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 69 * (codeMat 474 : Mat3).transpose = codeMat 386
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 197 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 197 (by decide)
    have hact : actionA (codeMat 273) (codeMat 395) (codeMat 197) = codeMat 66 := by
      unfold actionA
      rw [step103o279s28_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 197 * (codeMat 474 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 32 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 32 (by decide)
    have hact : actionA (codeMat 273) (codeMat 395) (codeMat 32) = codeMat 32 := by
      unfold actionA
      rw [step103o279s28_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 32 * (codeMat 474 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 40 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 40 (by decide)
    have hact : actionA (codeMat 273) (codeMat 395) (codeMat 40) = codeMat 16 := by
      unfold actionA
      rw [step103o279s28_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 40 * (codeMat 474 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 29 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 29 (by decide)
    have hact : actionA (codeMat 273) (codeMat 395) (codeMat 29) = codeMat 10 := by
      unfold actionA
      rw [step103o279s28_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 29 * (codeMat 474 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 395) (codeMat 1) = codeMat 6 := by
      unfold actionA
      rw [step103o279s28_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 474 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 3 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 3 (by decide)
    have hact : actionA (codeMat 273) (codeMat 395) (codeMat 3) = codeMat 1 := by
      unfold actionA
      rw [step103o279s28_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 3 * (codeMat 474 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s28_qr :
    QuotientRankAtLeast step103o279ActualSource28 12 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 395 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 395) orbit11W) 12 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 395) hP hQ orbit11W 12 orbit11_lb12
  exact quotientRankAtLeast_mono step103o279s28_source_le_transport hAct

-- Source 29: compressed row 29, orbit 3, action, lb 9
def step103o279ActualSource29 : Submodule F2 Mat3 := spanCodes [258, 130, 64, 32, 16, 10, 4, 1]

private theorem step103o279_o279W_le_src29 : o279W ≤ spanCodes [258, 130, 64, 32, 16, 10, 4, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 130, 64, 32, 16, 10, 4, 1] 68 (by decide)
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s29_QtInv :
    (codeMat 394 : Mat3).transpose⁻¹ = (codeMat 330 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 394 : Mat3).transpose * (codeMat 330 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s29_source_le_transport :
    step103o279ActualSource29 ≤ actionW (codeMat 84) (codeMat 394) flatW_3 := by
  apply step103o279_spanCodes_le_of_gens [258, 130, 64, 32, 16, 10, 4, 1]
    (actionW (codeMat 84) (codeMat 394) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 324 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 324 (by decide)
    have hact : actionA (codeMat 84) (codeMat 394) (codeMat 324) = codeMat 258 := by
      unfold actionA
      rw [step103o279s29_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 324 * (codeMat 330 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 325 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 325 (by decide)
    have hact : actionA (codeMat 84) (codeMat 394) (codeMat 325) = codeMat 130 := by
      unfold actionA
      rw [step103o279s29_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 325 * (codeMat 330 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 394) (codeMat 2) = codeMat 64 := by
      unfold actionA
      rw [step103o279s29_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 330 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 32 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 84) (codeMat 394) (codeMat 32) = codeMat 32 := by
      unfold actionA
      rw [step103o279s29_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 32 * (codeMat 330 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 40 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 84) (codeMat 394) (codeMat 40) = codeMat 16 := by
      unfold actionA
      rw [step103o279s29_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 40 * (codeMat 330 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 336 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 336 (by decide)
    have hact : actionA (codeMat 84) (codeMat 394) (codeMat 336) = codeMat 10 := by
      unfold actionA
      rw [step103o279s29_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 336 * (codeMat 330 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 394) (codeMat 256) = codeMat 4 := by
      unfold actionA
      rw [step103o279s29_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 330 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 128 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 394) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step103o279s29_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 330 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s29_qr :
    QuotientRankAtLeast step103o279ActualSource29 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 394 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 394) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 394) hP hQ flatW_3 9 flatSeed_3
  exact quotientRankAtLeast_mono step103o279s29_source_le_transport hAct

-- Source 30: compressed row 30, orbit 3, action, lb 9
def step103o279ActualSource30 : Submodule F2 Mat3 := spanCodes [256, 130, 66, 32, 16, 10, 6, 1]

private theorem step103o279_o279W_le_src30 : o279W ≤ spanCodes [256, 130, 66, 32, 16, 10, 6, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 130, 66, 32, 16, 10, 6, 1] 68 (by decide)
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s30_QtInv :
    (codeMat 206 : Mat3).transpose⁻¹ = (codeMat 498 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 206 : Mat3).transpose * (codeMat 498 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s30_source_le_transport :
    step103o279ActualSource30 ≤ actionW (codeMat 84) (codeMat 206) flatW_3 := by
  apply step103o279_spanCodes_le_of_gens [256, 130, 66, 32, 16, 10, 6, 1]
    (actionW (codeMat 84) (codeMat 206) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 1 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 206) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step103o279s30_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 498 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 325 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 325 (by decide)
    have hact : actionA (codeMat 84) (codeMat 206) (codeMat 325) = codeMat 130 := by
      unfold actionA
      rw [step103o279s30_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 325 * (codeMat 498 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 326 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 326 (by decide)
    have hact : actionA (codeMat 84) (codeMat 206) (codeMat 326) = codeMat 66 := by
      unfold actionA
      rw [step103o279s30_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 326 * (codeMat 498 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 206) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step103o279s30_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 498 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 40 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 84) (codeMat 206) (codeMat 40) = codeMat 16 := by
      unfold actionA
      rw [step103o279s30_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 40 * (codeMat 498 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 368 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 368 (by decide)
    have hact : actionA (codeMat 84) (codeMat 206) (codeMat 368) = codeMat 10 := by
      unfold actionA
      rw [step103o279s30_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 368 * (codeMat 498 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 206) (codeMat 256) = codeMat 6 := by
      unfold actionA
      rw [step103o279s30_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 498 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 206) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step103o279s30_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 498 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s30_qr :
    QuotientRankAtLeast step103o279ActualSource30 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 206 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 206) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 206) hP hQ flatW_3 9 flatSeed_3
  exact quotientRankAtLeast_mono step103o279s30_source_le_transport hAct

-- Source 31: compressed row 31, orbit 10, action, lb 12
def step103o279ActualSource31 : Submodule F2 Mat3 := spanCodes [256, 128, 68, 32, 16, 10, 1]

private theorem step103o279_o279W_le_src31 : o279W ≤ spanCodes [256, 128, 68, 32, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s31_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s31_source_le_transport :
    step103o279ActualSource31 ≤ actionW (codeMat 84) (codeMat 84) orbit10W := by
  apply step103o279_spanCodes_le_of_gens [256, 128, 68, 32, 16, 10, 1]
    (actionW (codeMat 84) (codeMat 84) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step103o279s31_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 84 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 2) = codeMat 128 := by
      unfold actionA
      rw [step103o279s31_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 84 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 68) = codeMat 68 := by
      unfold actionA
      rw [step103o279s31_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 68 * (codeMat 84 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step103o279s31_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 84 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 16) = codeMat 16 := by
      unfold actionA
      rw [step103o279s31_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 16 * (codeMat 84 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step103o279s31_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 160 * (codeMat 84 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step103o279s31_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 84 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s31_qr :
    QuotientRankAtLeast step103o279ActualSource31 12 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 84) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 84) hP hQ orbit10W 12 orbit10_lb12
  exact quotientRankAtLeast_mono step103o279s31_source_le_transport hAct

-- Source 32: compressed row 32, orbit 10, action, lb 12
def step103o279ActualSource32 : Submodule F2 Mat3 := spanCodes [260, 130, 68, 32, 16, 10, 1]

private theorem step103o279_o279W_le_src32 : o279W ≤ spanCodes [260, 130, 68, 32, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s32_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s32_source_le_transport :
    step103o279ActualSource32 ≤ actionW (codeMat 85) (codeMat 84) orbit10W := by
  apply step103o279_spanCodes_le_of_gens [260, 130, 68, 32, 16, 10, 1]
    (actionW (codeMat 85) (codeMat 84) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 85) (codeMat 84) (codeMat 1) = codeMat 260 := by
      unfold actionA
      rw [step103o279s32_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 1 * (codeMat 84 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 85) (codeMat 84) (codeMat 2) = codeMat 130 := by
      unfold actionA
      rw [step103o279s32_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 2 * (codeMat 84 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 324 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 324 (by decide)
    have hact : actionA (codeMat 85) (codeMat 84) (codeMat 324) = codeMat 68 := by
      unfold actionA
      rw [step103o279s32_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 324 * (codeMat 84 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 85) (codeMat 84) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step103o279s32_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 8 * (codeMat 84 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 85) (codeMat 84) (codeMat 16) = codeMat 16 := by
      unfold actionA
      rw [step103o279s32_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 16 * (codeMat 84 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 85) (codeMat 84) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step103o279s32_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 160 * (codeMat 84 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 85) (codeMat 84) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step103o279s32_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 256 * (codeMat 84 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s32_qr :
    QuotientRankAtLeast step103o279ActualSource32 12 := by
  have hP : Invertible (codeMat 85 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 85) (codeMat 84) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 85) (codeMat 84) hP hQ orbit10W 12 orbit10_lb12
  exact quotientRankAtLeast_mono step103o279s32_source_le_transport hAct

-- Source 33: compressed row 33, orbit 3, action, lb 9
def step103o279ActualSource33 : Submodule F2 Mat3 := spanCodes [258, 128, 66, 32, 16, 10, 6, 1]

private theorem step103o279_o279W_le_src33 : o279W ≤ spanCodes [258, 128, 66, 32, 16, 10, 6, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 128, 66, 32, 16, 10, 6, 1] 68 (by decide)
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s33_QtInv :
    (codeMat 334 : Mat3).transpose⁻¹ = (codeMat 442 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 334 : Mat3).transpose * (codeMat 442 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s33_source_le_transport :
    step103o279ActualSource33 ≤ actionW (codeMat 84) (codeMat 334) flatW_3 := by
  apply step103o279_spanCodes_le_of_gens [258, 128, 66, 32, 16, 10, 6, 1]
    (actionW (codeMat 84) (codeMat 334) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 69 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 69 (by decide)
    have hact : actionA (codeMat 84) (codeMat 334) (codeMat 69) = codeMat 258 := by
      unfold actionA
      rw [step103o279s33_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 69 * (codeMat 442 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 334) (codeMat 1) = codeMat 128 := by
      unfold actionA
      rw [step103o279s33_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 442 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 70 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 70 (by decide)
    have hact : actionA (codeMat 84) (codeMat 334) (codeMat 70) = codeMat 66 := by
      unfold actionA
      rw [step103o279s33_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 70 * (codeMat 442 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 40 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 84) (codeMat 334) (codeMat 40) = codeMat 32 := by
      unfold actionA
      rw [step103o279s33_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 40 * (codeMat 442 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 334) (codeMat 8) = codeMat 16 := by
      unfold actionA
      rw [step103o279s33_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 442 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 112 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 112 (by decide)
    have hact : actionA (codeMat 84) (codeMat 334) (codeMat 112) = codeMat 10 := by
      unfold actionA
      rw [step103o279s33_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 112 * (codeMat 442 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 334) (codeMat 256) = codeMat 6 := by
      unfold actionA
      rw [step103o279s33_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 442 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 334) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step103o279s33_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 442 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s33_qr :
    QuotientRankAtLeast step103o279ActualSource33 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 334 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 334) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 334) hP hQ flatW_3 9 flatSeed_3
  exact quotientRankAtLeast_mono step103o279s33_source_le_transport hAct

-- Source 34: compressed row 34, orbit 3, action, lb 9
def step103o279ActualSource34 : Submodule F2 Mat3 := spanCodes [258, 128, 64, 32, 16, 10, 4, 1]

private theorem step103o279_o279W_le_src34 : o279W ≤ spanCodes [258, 128, 64, 32, 16, 10, 4, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 128, 64, 32, 16, 10, 4, 1] 68 (by decide)
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s34_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s34_source_le_transport :
    step103o279ActualSource34 ≤ actionW (codeMat 84) (codeMat 266) flatW_3 := by
  apply step103o279_spanCodes_le_of_gens [258, 128, 64, 32, 16, 10, 4, 1]
    (actionW (codeMat 84) (codeMat 266) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 68 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 68 (by decide)
    have hact : actionA (codeMat 84) (codeMat 266) (codeMat 68) = codeMat 258 := by
      unfold actionA
      rw [step103o279s34_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 68 * (codeMat 266 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 266) (codeMat 1) = codeMat 128 := by
      unfold actionA
      rw [step103o279s34_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 266) (codeMat 2) = codeMat 64 := by
      unfold actionA
      rw [step103o279s34_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 266 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 32 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 84) (codeMat 266) (codeMat 32) = codeMat 32 := by
      unfold actionA
      rw [step103o279s34_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 32 * (codeMat 266 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 266) (codeMat 8) = codeMat 16 := by
      unfold actionA
      rw [step103o279s34_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 266 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 80 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 80 (by decide)
    have hact : actionA (codeMat 84) (codeMat 266) (codeMat 80) = codeMat 10 := by
      unfold actionA
      rw [step103o279s34_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 80 * (codeMat 266 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 266) (codeMat 256) = codeMat 4 := by
      unfold actionA
      rw [step103o279s34_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 266 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 128 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 266) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step103o279s34_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s34_qr :
    QuotientRankAtLeast step103o279ActualSource34 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 266) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 266) hP hQ flatW_3 9 flatSeed_3
  exact quotientRankAtLeast_mono step103o279s34_source_le_transport hAct

-- Source 35: compressed row 35, orbit 150, action, lb 16
def step103o279ActualSource35 : Submodule F2 Mat3 := spanCodes [262, 68, 16, 10, 1]

private theorem step103o279_o279W_le_src35 : o279W ≤ spanCodes [262, 68, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s35_QtInv :
    (codeMat 277 : Mat3).transpose⁻¹ = (codeMat 277 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 277 : Mat3).transpose * (codeMat 277 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s35_source_le_transport :
    step103o279ActualSource35 ≤ actionW (codeMat 273) (codeMat 277) o150W := by
  apply step103o279_spanCodes_le_of_gens [262, 68, 16, 10, 1]
    (actionW (codeMat 273) (codeMat 277) o150W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 327 ∈ o150W :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 16, 10, 1] 327 (by decide)
    have hact : actionA (codeMat 273) (codeMat 277) (codeMat 327) = codeMat 262 := by
      unfold actionA
      rw [step103o279s35_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 327 * (codeMat 277 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 69 ∈ o150W :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 16, 10, 1] 69 (by decide)
    have hact : actionA (codeMat 273) (codeMat 277) (codeMat 69) = codeMat 68 := by
      unfold actionA
      rw [step103o279s35_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 69 * (codeMat 277 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 16 ∈ o150W :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 273) (codeMat 277) (codeMat 16) = codeMat 16 := by
      unfold actionA
      rw [step103o279s35_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 16 * (codeMat 277 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 10 ∈ o150W :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 16, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 273) (codeMat 277) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step103o279s35_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 10 * (codeMat 277 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o150W :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 277) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step103o279s35_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 277 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s35_qr :
    QuotientRankAtLeast step103o279ActualSource35 16 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 277 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 277) o150W) 16 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 277) hP hQ o150W 16 step99_orbit150_lb16_unconditional
  exact quotientRankAtLeast_mono step103o279s35_source_le_transport hAct

-- Source 36: compressed row 36, orbit 120, action, lb 15
def step103o279ActualSource36 : Submodule F2 Mat3 := spanCodes [68, 32, 16, 10, 1]

private theorem step103o279_o279W_le_src36 : o279W ≤ spanCodes [68, 32, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s36_QtInv :
    (codeMat 98 : Mat3).transpose⁻¹ = (codeMat 140 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 98 : Mat3).transpose * (codeMat 140 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s36_source_le_transport :
    step103o279ActualSource36 ≤ actionW (codeMat 266) (codeMat 98) o120W := by
  apply step103o279_spanCodes_le_of_gens [68, 32, 16, 10, 1]
    (actionW (codeMat 266) (codeMat 98) o120W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 272 ∈ o120W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 32, 12, 2, 1] 272 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 272) = codeMat 68 := by
      unfold actionA
      rw [step103o279s36_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 272 * (codeMat 140 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ o120W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 32, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 2) = codeMat 32 := by
      unfold actionA
      rw [step103o279s36_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 140 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ o120W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step103o279s36_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 140 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 12 ∈ o120W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 32, 12, 2, 1] 12 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 12) = codeMat 10 := by
      unfold actionA
      rw [step103o279s36_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 12 * (codeMat 140 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 32 ∈ o120W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 32, 12, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step103o279s36_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 140 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s36_qr :
    QuotientRankAtLeast step103o279ActualSource36 15 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 98) o120W) 15 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 98) hP hQ o120W 15 step99_orbit120_lb15_unconditional
  exact quotientRankAtLeast_mono step103o279s36_source_le_transport hAct

-- Source 37: compressed row 37, orbit 65, action, lb 15
def step103o279ActualSource37 : Submodule F2 Mat3 := spanCodes [292, 160, 68, 16, 10, 1]

private theorem step103o279_o279W_le_src37 : o279W ≤ spanCodes [292, 160, 68, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s37_QtInv :
    (codeMat 282 : Mat3).transpose⁻¹ = (codeMat 267 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 282 : Mat3).transpose * (codeMat 267 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s37_source_le_transport :
    step103o279ActualSource37 ≤ actionW (codeMat 267) (codeMat 282) o65W := by
  apply step103o279_spanCodes_le_of_gens [292, 160, 68, 16, 10, 1]
    (actionW (codeMat 267) (codeMat 282) o65W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 260 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 260 (by decide)
    have hact : actionA (codeMat 267) (codeMat 282) (codeMat 260) = codeMat 292 := by
      unfold actionA
      rw [step103o279s37_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 260 * (codeMat 267 : Mat3).transpose = codeMat 292
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 228 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 228 (by decide)
    have hact : actionA (codeMat 267) (codeMat 282) (codeMat 228) = codeMat 160 := by
      unfold actionA
      rw [step103o279s37_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 228 * (codeMat 267 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 160 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 267) (codeMat 282) (codeMat 160) = codeMat 68 := by
      unfold actionA
      rw [step103o279s37_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 160 * (codeMat 267 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 27 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 27 (by decide)
    have hact : actionA (codeMat 267) (codeMat 282) (codeMat 27) = codeMat 16 := by
      unfold actionA
      rw [step103o279s37_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 27 * (codeMat 267 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 10 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 267) (codeMat 282) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step103o279s37_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 10 * (codeMat 267 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 267) (codeMat 282) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step103o279s37_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 16 * (codeMat 267 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s37_qr :
    QuotientRankAtLeast step103o279ActualSource37 15 := by
  have hP : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 282 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 267) (codeMat 282) o65W) 15 :=
    @quotientRankAtLeast_action (codeMat 267) (codeMat 282) hP hQ o65W 15 step99_orbit65_lb15_unconditional
  exact quotientRankAtLeast_mono step103o279s37_source_le_transport hAct

-- Source 38: compressed row 38, orbit 11, action, lb 12
def step103o279ActualSource38 : Submodule F2 Mat3 := spanCodes [258, 64, 34, 16, 10, 4, 1]

private theorem step103o279_o279W_le_src38 : o279W ≤ spanCodes [258, 64, 34, 16, 10, 4, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 64, 34, 16, 10, 4, 1] 68 (by decide)
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s38_QtInv :
    (codeMat 172 : Mat3).transpose⁻¹ = (codeMat 99 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 172 : Mat3).transpose * (codeMat 99 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s38_source_le_transport :
    step103o279ActualSource38 ≤ actionW (codeMat 273) (codeMat 172) orbit11W := by
  apply step103o279_spanCodes_le_of_gens [258, 64, 34, 16, 10, 4, 1]
    (actionW (codeMat 273) (codeMat 172) orbit11W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 196 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 196 (by decide)
    have hact : actionA (codeMat 273) (codeMat 172) (codeMat 196) = codeMat 258 := by
      unfold actionA
      rw [step103o279s38_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 196 * (codeMat 99 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 128 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 128 (by decide)
    have hact : actionA (codeMat 273) (codeMat 172) (codeMat 128) = codeMat 64 := by
      unfold actionA
      rw [step103o279s38_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 128 * (codeMat 99 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 28 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 28 (by decide)
    have hact : actionA (codeMat 273) (codeMat 172) (codeMat 28) = codeMat 34 := by
      unfold actionA
      rw [step103o279s38_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 28 * (codeMat 99 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 32 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 32 (by decide)
    have hact : actionA (codeMat 273) (codeMat 172) (codeMat 32) = codeMat 16 := by
      unfold actionA
      rw [step103o279s38_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 32 * (codeMat 99 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 20 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 20 (by decide)
    have hact : actionA (codeMat 273) (codeMat 172) (codeMat 20) = codeMat 10 := by
      unfold actionA
      rw [step103o279s38_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 20 * (codeMat 99 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 3 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 3 (by decide)
    have hact : actionA (codeMat 273) (codeMat 172) (codeMat 3) = codeMat 4 := by
      unfold actionA
      rw [step103o279s38_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 3 * (codeMat 99 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 172) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step103o279s38_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 99 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s38_qr :
    QuotientRankAtLeast step103o279ActualSource38 12 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 172 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 172) orbit11W) 12 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 172) hP hQ orbit11W 12 orbit11_lb12
  exact quotientRankAtLeast_mono step103o279s38_source_le_transport hAct

-- Source 39: compressed row 39, orbit 14, action, lb 12
def step103o279ActualSource39 : Submodule F2 Mat3 := spanCodes [256, 134, 68, 34, 16, 10, 1]

private theorem step103o279_o279W_le_src39 : o279W ≤ spanCodes [256, 134, 68, 34, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s39_QtInv :
    (codeMat 485 : Mat3).transpose⁻¹ = (codeMat 171 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 485 : Mat3).transpose * (codeMat 171 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s39_source_le_transport :
    step103o279ActualSource39 ≤ actionW (codeMat 157) (codeMat 485) orbit14W := by
  apply step103o279_spanCodes_le_of_gens [256, 134, 68, 34, 16, 10, 1]
    (actionW (codeMat 157) (codeMat 485) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 511 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 511 (by decide)
    have hact : actionA (codeMat 157) (codeMat 485) (codeMat 511) = codeMat 256 := by
      unfold actionA
      rw [step103o279s39_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 511 * (codeMat 171 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 508 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 508 (by decide)
    have hact : actionA (codeMat 157) (codeMat 485) (codeMat 508) = codeMat 134 := by
      unfold actionA
      rw [step103o279s39_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 508 * (codeMat 171 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 149 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 149 (by decide)
    have hact : actionA (codeMat 157) (codeMat 485) (codeMat 149) = codeMat 68 := by
      unfold actionA
      rw [step103o279s39_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 149 * (codeMat 171 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 224 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 224 (by decide)
    have hact : actionA (codeMat 157) (codeMat 485) (codeMat 224) = codeMat 34 := by
      unfold actionA
      rw [step103o279s39_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 224 * (codeMat 171 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 157) (codeMat 485) (codeMat 256) = codeMat 16 := by
      unfold actionA
      rw [step103o279s39_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 256 * (codeMat 171 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 157) (codeMat 485) (codeMat 96) = codeMat 10 := by
      unfold actionA
      rw [step103o279s39_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 96 * (codeMat 171 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 157) (codeMat 485) (codeMat 360) = codeMat 1 := by
      unfold actionA
      rw [step103o279s39_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 360 * (codeMat 171 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s39_qr :
    QuotientRankAtLeast step103o279ActualSource39 12 := by
  have hP : Invertible (codeMat 157 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 485 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 157) (codeMat 485) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 157) (codeMat 485) hP hQ orbit14W 12 orbit14_lb12
  exact quotientRankAtLeast_mono step103o279s39_source_le_transport hAct

-- Source 40: compressed row 40, orbit 11, action, lb 12
def step103o279ActualSource40 : Submodule F2 Mat3 := spanCodes [384, 66, 34, 16, 10, 6, 1]

private theorem step103o279_o279W_le_src40 : o279W ≤ spanCodes [384, 66, 34, 16, 10, 6, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [384, 66, 34, 16, 10, 6, 1] 68 (by decide)
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s40_QtInv :
    (codeMat 425 : Mat3).transpose⁻¹ = (codeMat 249 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 425 : Mat3).transpose * (codeMat 249 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s40_source_le_transport :
    step103o279ActualSource40 ≤ actionW (codeMat 273) (codeMat 425) orbit11W := by
  apply step103o279_spanCodes_le_of_gens [384, 66, 34, 16, 10, 6, 1]
    (actionW (codeMat 273) (codeMat 425) orbit11W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 128 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 128 (by decide)
    have hact : actionA (codeMat 273) (codeMat 425) (codeMat 128) = codeMat 384 := by
      unfold actionA
      rw [step103o279s40_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 128 * (codeMat 249 : Mat3).transpose = codeMat 384
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 196 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 196 (by decide)
    have hact : actionA (codeMat 273) (codeMat 425) (codeMat 196) = codeMat 66 := by
      unfold actionA
      rw [step103o279s40_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 196 * (codeMat 249 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 52 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 52 (by decide)
    have hact : actionA (codeMat 273) (codeMat 425) (codeMat 52) = codeMat 34 := by
      unfold actionA
      rw [step103o279s40_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 52 * (codeMat 249 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 32 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 32 (by decide)
    have hact : actionA (codeMat 273) (codeMat 425) (codeMat 32) = codeMat 16 := by
      unfold actionA
      rw [step103o279s40_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 32 * (codeMat 249 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 28 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 28 (by decide)
    have hact : actionA (codeMat 273) (codeMat 425) (codeMat 28) = codeMat 10 := by
      unfold actionA
      rw [step103o279s40_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 28 * (codeMat 249 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 425) (codeMat 2) = codeMat 6 := by
      unfold actionA
      rw [step103o279s40_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 249 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 3 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 3 (by decide)
    have hact : actionA (codeMat 273) (codeMat 425) (codeMat 3) = codeMat 1 := by
      unfold actionA
      rw [step103o279s40_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 3 * (codeMat 249 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s40_qr :
    QuotientRankAtLeast step103o279ActualSource40 12 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 425 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 425) orbit11W) 12 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 425) hP hQ orbit11W 12 orbit11_lb12
  exact quotientRankAtLeast_mono step103o279s40_source_le_transport hAct

-- Source 41: compressed row 41, orbit 10, action, lb 12
def step103o279ActualSource41 : Submodule F2 Mat3 := spanCodes [260, 128, 68, 34, 16, 10, 1]

private theorem step103o279_o279W_le_src41 : o279W ≤ spanCodes [260, 128, 68, 34, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s41_QtInv :
    (codeMat 340 : Mat3).transpose⁻¹ = (codeMat 85 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 340 : Mat3).transpose * (codeMat 85 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s41_source_le_transport :
    step103o279ActualSource41 ≤ actionW (codeMat 84) (codeMat 340) orbit10W := by
  apply step103o279_spanCodes_le_of_gens [260, 128, 68, 34, 16, 10, 1]
    (actionW (codeMat 84) (codeMat 340) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 325 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 325 (by decide)
    have hact : actionA (codeMat 84) (codeMat 340) (codeMat 325) = codeMat 260 := by
      unfold actionA
      rw [step103o279s41_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 325 * (codeMat 85 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 340) (codeMat 2) = codeMat 128 := by
      unfold actionA
      rw [step103o279s41_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 85 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 324 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 324 (by decide)
    have hact : actionA (codeMat 84) (codeMat 340) (codeMat 324) = codeMat 68 := by
      unfold actionA
      rw [step103o279s41_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 324 * (codeMat 85 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 168 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 168 (by decide)
    have hact : actionA (codeMat 84) (codeMat 340) (codeMat 168) = codeMat 34 := by
      unfold actionA
      rw [step103o279s41_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 168 * (codeMat 85 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 84) (codeMat 340) (codeMat 16) = codeMat 16 := by
      unfold actionA
      rw [step103o279s41_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 16 * (codeMat 85 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 84) (codeMat 340) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step103o279s41_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 160 * (codeMat 85 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 340) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step103o279s41_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 85 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s41_qr :
    QuotientRankAtLeast step103o279ActualSource41 12 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 340 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 340) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 340) hP hQ orbit10W 12 orbit10_lb12
  exact quotientRankAtLeast_mono step103o279s41_source_le_transport hAct

-- Source 42: compressed row 42, orbit 3, action, lb 9
def step103o279ActualSource42 : Submodule F2 Mat3 := spanCodes [258, 128, 64, 34, 16, 10, 4, 1]

private theorem step103o279_o279W_le_src42 : o279W ≤ spanCodes [258, 128, 64, 34, 16, 10, 4, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 128, 64, 34, 16, 10, 4, 1] 68 (by decide)
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s42_QtInv :
    (codeMat 298 : Mat3).transpose⁻¹ = (codeMat 270 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 298 : Mat3).transpose * (codeMat 270 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s42_source_le_transport :
    step103o279ActualSource42 ≤ actionW (codeMat 84) (codeMat 298) flatW_3 := by
  apply step103o279_spanCodes_le_of_gens [258, 128, 64, 34, 16, 10, 4, 1]
    (actionW (codeMat 84) (codeMat 298) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 70 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 70 (by decide)
    have hact : actionA (codeMat 84) (codeMat 298) (codeMat 70) = codeMat 258 := by
      unfold actionA
      rw [step103o279s42_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 70 * (codeMat 270 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 298) (codeMat 1) = codeMat 128 := by
      unfold actionA
      rw [step103o279s42_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 270 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 298) (codeMat 2) = codeMat 64 := by
      unfold actionA
      rw [step103o279s42_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 270 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 112 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 112 (by decide)
    have hact : actionA (codeMat 84) (codeMat 298) (codeMat 112) = codeMat 34 := by
      unfold actionA
      rw [step103o279s42_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 112 * (codeMat 270 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 298) (codeMat 8) = codeMat 16 := by
      unfold actionA
      rw [step103o279s42_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 270 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 80 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 80 (by decide)
    have hact : actionA (codeMat 84) (codeMat 298) (codeMat 80) = codeMat 10 := by
      unfold actionA
      rw [step103o279s42_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 80 * (codeMat 270 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 298) (codeMat 384) = codeMat 4 := by
      unfold actionA
      rw [step103o279s42_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 270 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 128 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 298) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step103o279s42_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 270 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s42_qr :
    QuotientRankAtLeast step103o279ActualSource42 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 298 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 298) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 298) hP hQ flatW_3 9 flatSeed_3
  exact quotientRankAtLeast_mono step103o279s42_source_le_transport hAct

-- Source 43: compressed row 43, orbit 3, action, lb 9
def step103o279ActualSource43 : Submodule F2 Mat3 := spanCodes [258, 130, 64, 34, 16, 10, 4, 1]

private theorem step103o279_o279W_le_src43 : o279W ≤ spanCodes [258, 130, 64, 34, 16, 10, 4, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 130, 64, 34, 16, 10, 4, 1] 68 (by decide)
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s43_QtInv :
    (codeMat 426 : Mat3).transpose⁻¹ = (codeMat 335 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 426 : Mat3).transpose * (codeMat 335 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s43_source_le_transport :
    step103o279ActualSource43 ≤ actionW (codeMat 84) (codeMat 426) flatW_3 := by
  apply step103o279_spanCodes_le_of_gens [258, 130, 64, 34, 16, 10, 4, 1]
    (actionW (codeMat 84) (codeMat 426) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 326 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 326 (by decide)
    have hact : actionA (codeMat 84) (codeMat 426) (codeMat 326) = codeMat 258 := by
      unfold actionA
      rw [step103o279s43_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 326 * (codeMat 335 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 325 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 325 (by decide)
    have hact : actionA (codeMat 84) (codeMat 426) (codeMat 325) = codeMat 130 := by
      unfold actionA
      rw [step103o279s43_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 325 * (codeMat 335 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 426) (codeMat 2) = codeMat 64 := by
      unfold actionA
      rw [step103o279s43_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 335 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 368 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 368 (by decide)
    have hact : actionA (codeMat 84) (codeMat 426) (codeMat 368) = codeMat 34 := by
      unfold actionA
      rw [step103o279s43_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 368 * (codeMat 335 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 40 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 84) (codeMat 426) (codeMat 40) = codeMat 16 := by
      unfold actionA
      rw [step103o279s43_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 40 * (codeMat 335 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 336 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 336 (by decide)
    have hact : actionA (codeMat 84) (codeMat 426) (codeMat 336) = codeMat 10 := by
      unfold actionA
      rw [step103o279s43_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 336 * (codeMat 335 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 426) (codeMat 384) = codeMat 4 := by
      unfold actionA
      rw [step103o279s43_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 335 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 128 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 426) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step103o279s43_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 335 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s43_qr :
    QuotientRankAtLeast step103o279ActualSource43 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 426 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 426) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 426) hP hQ flatW_3 9 flatSeed_3
  exact quotientRankAtLeast_mono step103o279s43_source_le_transport hAct

-- Source 44: compressed row 44, orbit 14, action, lb 12
def step103o279ActualSource44 : Submodule F2 Mat3 := spanCodes [256, 132, 68, 32, 16, 10, 1]

private theorem step103o279_o279W_le_src44 : o279W ≤ spanCodes [256, 132, 68, 32, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s44_QtInv :
    (codeMat 225 : Mat3).transpose⁻¹ = (codeMat 169 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 225 : Mat3).transpose * (codeMat 169 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s44_source_le_transport :
    step103o279ActualSource44 ≤ actionW (codeMat 156) (codeMat 225) orbit14W := by
  apply step103o279_spanCodes_le_of_gens [256, 132, 68, 32, 16, 10, 1]
    (actionW (codeMat 156) (codeMat 225) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 156) (codeMat 225) (codeMat 2) = codeMat 256 := by
      unfold actionA
      rw [step103o279s44_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 2 * (codeMat 169 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 148 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 148 (by decide)
    have hact : actionA (codeMat 156) (codeMat 225) (codeMat 148) = codeMat 132 := by
      unfold actionA
      rw [step103o279s44_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 148 * (codeMat 169 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 149 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 149 (by decide)
    have hact : actionA (codeMat 156) (codeMat 225) (codeMat 149) = codeMat 68 := by
      unfold actionA
      rw [step103o279s44_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 149 * (codeMat 169 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 156) (codeMat 225) (codeMat 128) = codeMat 32 := by
      unfold actionA
      rw [step103o279s44_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 128 * (codeMat 169 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 156) (codeMat 225) (codeMat 256) = codeMat 16 := by
      unfold actionA
      rw [step103o279s44_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 256 * (codeMat 169 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 156) (codeMat 225) (codeMat 96) = codeMat 10 := by
      unfold actionA
      rw [step103o279s44_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 96 * (codeMat 169 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 156) (codeMat 225) (codeMat 360) = codeMat 1 := by
      unfold actionA
      rw [step103o279s44_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 360 * (codeMat 169 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s44_qr :
    QuotientRankAtLeast step103o279ActualSource44 12 := by
  have hP : Invertible (codeMat 156 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 156) (codeMat 225) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 156) (codeMat 225) hP hQ orbit14W 12 orbit14_lb12
  exact quotientRankAtLeast_mono step103o279s44_source_le_transport hAct

-- Source 45: compressed row 45, orbit 120, transpose, lb 15
def step103o279ActualSource45 : Submodule F2 Mat3 := spanCodes [132, 68, 16, 10, 1]

private theorem step103o279_o279W_le_src45 : o279W ≤ spanCodes [132, 68, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s45_QtInv :
    (codeMat 282 : Mat3).transpose⁻¹ = (codeMat 267 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 282 : Mat3).transpose * (codeMat 267 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s45_source_le_transport :
    step103o279ActualSource45 ≤ actionW (codeMat 99) (codeMat 282) (transposeW o120W) := by
  apply step103o279_spanCodes_le_of_gens [132, 68, 16, 10, 1]
    (actionW (codeMat 99) (codeMat 282) (transposeW o120W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw0 : codeMat 274 ∈ o120W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 32, 12, 2, 1] 274 (by decide)
    have hwT : (codeMat 274 : Mat3).transpose = codeMat 280 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hw : codeMat 280 ∈ transposeW o120W :=
      step103o279_codeMat_mem_transposeW_of_witness hw0 hwT
    have hact : actionA (codeMat 99) (codeMat 282) (codeMat 280) = codeMat 132 := by
      unfold actionA
      rw [step103o279s45_QtInv]
      show (codeMat 99 : Mat3).transpose * codeMat 280 * (codeMat 267 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw0 : codeMat 272 ∈ o120W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 32, 12, 2, 1] 272 (by decide)
    have hwT : (codeMat 272 : Mat3).transpose = codeMat 272 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hw : codeMat 272 ∈ transposeW o120W :=
      step103o279_codeMat_mem_transposeW_of_witness hw0 hwT
    have hact : actionA (codeMat 99) (codeMat 282) (codeMat 272) = codeMat 68 := by
      unfold actionA
      rw [step103o279s45_QtInv]
      show (codeMat 99 : Mat3).transpose * codeMat 272 * (codeMat 267 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw0 : codeMat 45 ∈ o120W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 32, 12, 2, 1] 45 (by decide)
    have hwT : (codeMat 45 : Mat3).transpose = codeMat 195 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hw : codeMat 195 ∈ transposeW o120W :=
      step103o279_codeMat_mem_transposeW_of_witness hw0 hwT
    have hact : actionA (codeMat 99) (codeMat 282) (codeMat 195) = codeMat 16 := by
      unfold actionA
      rw [step103o279s45_QtInv]
      show (codeMat 99 : Mat3).transpose * codeMat 195 * (codeMat 267 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw0 : codeMat 12 ∈ o120W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 32, 12, 2, 1] 12 (by decide)
    have hwT : (codeMat 12 : Mat3).transpose = codeMat 66 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hw : codeMat 66 ∈ transposeW o120W :=
      step103o279_codeMat_mem_transposeW_of_witness hw0 hwT
    have hact : actionA (codeMat 99) (codeMat 282) (codeMat 66) = codeMat 10 := by
      unfold actionA
      rw [step103o279s45_QtInv]
      show (codeMat 99 : Mat3).transpose * codeMat 66 * (codeMat 267 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw0 : codeMat 32 ∈ o120W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 32, 12, 2, 1] 32 (by decide)
    have hwT : (codeMat 32 : Mat3).transpose = codeMat 128 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hw : codeMat 128 ∈ transposeW o120W :=
      step103o279_codeMat_mem_transposeW_of_witness hw0 hwT
    have hact : actionA (codeMat 99) (codeMat 282) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step103o279s45_QtInv]
      show (codeMat 99 : Mat3).transpose * codeMat 128 * (codeMat 267 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s45_qr :
    QuotientRankAtLeast step103o279ActualSource45 15 := by
  have hP : Invertible (codeMat 99 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 282 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hT : QuotientRankAtLeast (transposeW o120W) 15 :=
    quotientRankAtLeast_transpose step99_orbit120_lb15_unconditional
  have hAct : QuotientRankAtLeast (actionW (codeMat 99) (codeMat 282) (transposeW o120W)) 15 :=
    @quotientRankAtLeast_action (codeMat 99) (codeMat 282) hP hQ (transposeW o120W) 15 hT
  exact quotientRankAtLeast_mono step103o279s45_source_le_transport hAct

-- Source 46: compressed row 46, orbit 120, transpose, lb 15
def step103o279ActualSource46 : Submodule F2 Mat3 := spanCodes [134, 68, 16, 10, 1]

private theorem step103o279_o279W_le_src46 : o279W ≤ spanCodes [134, 68, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s46_QtInv :
    (codeMat 282 : Mat3).transpose⁻¹ = (codeMat 267 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 282 : Mat3).transpose * (codeMat 267 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s46_source_le_transport :
    step103o279ActualSource46 ≤ actionW (codeMat 107) (codeMat 282) (transposeW o120W) := by
  apply step103o279_spanCodes_le_of_gens [134, 68, 16, 10, 1]
    (actionW (codeMat 107) (codeMat 282) (transposeW o120W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw0 : codeMat 274 ∈ o120W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 32, 12, 2, 1] 274 (by decide)
    have hwT : (codeMat 274 : Mat3).transpose = codeMat 280 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hw : codeMat 280 ∈ transposeW o120W :=
      step103o279_codeMat_mem_transposeW_of_witness hw0 hwT
    have hact : actionA (codeMat 107) (codeMat 282) (codeMat 280) = codeMat 134 := by
      unfold actionA
      rw [step103o279s46_QtInv]
      show (codeMat 107 : Mat3).transpose * codeMat 280 * (codeMat 267 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw0 : codeMat 304 ∈ o120W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 32, 12, 2, 1] 304 (by decide)
    have hwT : (codeMat 304 : Mat3).transpose = codeMat 400 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hw : codeMat 400 ∈ transposeW o120W :=
      step103o279_codeMat_mem_transposeW_of_witness hw0 hwT
    have hact : actionA (codeMat 107) (codeMat 282) (codeMat 400) = codeMat 68 := by
      unfold actionA
      rw [step103o279s46_QtInv]
      show (codeMat 107 : Mat3).transpose * codeMat 400 * (codeMat 267 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw0 : codeMat 45 ∈ o120W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 32, 12, 2, 1] 45 (by decide)
    have hwT : (codeMat 45 : Mat3).transpose = codeMat 195 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hw : codeMat 195 ∈ transposeW o120W :=
      step103o279_codeMat_mem_transposeW_of_witness hw0 hwT
    have hact : actionA (codeMat 107) (codeMat 282) (codeMat 195) = codeMat 16 := by
      unfold actionA
      rw [step103o279s46_QtInv]
      show (codeMat 107 : Mat3).transpose * codeMat 195 * (codeMat 267 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw0 : codeMat 12 ∈ o120W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 32, 12, 2, 1] 12 (by decide)
    have hwT : (codeMat 12 : Mat3).transpose = codeMat 66 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hw : codeMat 66 ∈ transposeW o120W :=
      step103o279_codeMat_mem_transposeW_of_witness hw0 hwT
    have hact : actionA (codeMat 107) (codeMat 282) (codeMat 66) = codeMat 10 := by
      unfold actionA
      rw [step103o279s46_QtInv]
      show (codeMat 107 : Mat3).transpose * codeMat 66 * (codeMat 267 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw0 : codeMat 32 ∈ o120W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 32, 12, 2, 1] 32 (by decide)
    have hwT : (codeMat 32 : Mat3).transpose = codeMat 128 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hw : codeMat 128 ∈ transposeW o120W :=
      step103o279_codeMat_mem_transposeW_of_witness hw0 hwT
    have hact : actionA (codeMat 107) (codeMat 282) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step103o279s46_QtInv]
      show (codeMat 107 : Mat3).transpose * codeMat 128 * (codeMat 267 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s46_qr :
    QuotientRankAtLeast step103o279ActualSource46 15 := by
  have hP : Invertible (codeMat 107 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 282 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hT : QuotientRankAtLeast (transposeW o120W) 15 :=
    quotientRankAtLeast_transpose step99_orbit120_lb15_unconditional
  have hAct : QuotientRankAtLeast (actionW (codeMat 107) (codeMat 282) (transposeW o120W)) 15 :=
    @quotientRankAtLeast_action (codeMat 107) (codeMat 282) hP hQ (transposeW o120W) 15 hT
  exact quotientRankAtLeast_mono step103o279s46_source_le_transport hAct

-- Source 47: compressed row 47, orbit 10, action, lb 12
def step103o279ActualSource47 : Submodule F2 Mat3 := spanCodes [256, 130, 68, 34, 16, 10, 1]

private theorem step103o279_o279W_le_src47 : o279W ≤ spanCodes [256, 130, 68, 34, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s47_QtInv :
    (codeMat 340 : Mat3).transpose⁻¹ = (codeMat 85 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 340 : Mat3).transpose * (codeMat 85 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s47_source_le_transport :
    step103o279ActualSource47 ≤ actionW (codeMat 85) (codeMat 340) orbit10W := by
  apply step103o279_spanCodes_le_of_gens [256, 130, 68, 34, 16, 10, 1]
    (actionW (codeMat 85) (codeMat 340) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 325 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 325 (by decide)
    have hact : actionA (codeMat 85) (codeMat 340) (codeMat 325) = codeMat 256 := by
      unfold actionA
      rw [step103o279s47_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 325 * (codeMat 85 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 85) (codeMat 340) (codeMat 2) = codeMat 130 := by
      unfold actionA
      rw [step103o279s47_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 2 * (codeMat 85 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 85) (codeMat 340) (codeMat 68) = codeMat 68 := by
      unfold actionA
      rw [step103o279s47_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 68 * (codeMat 85 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 168 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 168 (by decide)
    have hact : actionA (codeMat 85) (codeMat 340) (codeMat 168) = codeMat 34 := by
      unfold actionA
      rw [step103o279s47_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 168 * (codeMat 85 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 85) (codeMat 340) (codeMat 16) = codeMat 16 := by
      unfold actionA
      rw [step103o279s47_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 16 * (codeMat 85 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 85) (codeMat 340) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step103o279s47_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 160 * (codeMat 85 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 85) (codeMat 340) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step103o279s47_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 256 * (codeMat 85 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s47_qr :
    QuotientRankAtLeast step103o279ActualSource47 12 := by
  have hP : Invertible (codeMat 85 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 340 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 85) (codeMat 340) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 85) (codeMat 340) hP hQ orbit10W 12 orbit10_lb12
  exact quotientRankAtLeast_mono step103o279s47_source_le_transport hAct

-- Source 48: compressed row 48, orbit 14, action, lb 12
def step103o279ActualSource48 : Submodule F2 Mat3 := spanCodes [262, 130, 68, 36, 16, 10, 1]

private theorem step103o279_o279W_le_src48 : o279W ≤ spanCodes [262, 130, 68, 36, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s48_QtInv :
    (codeMat 355 : Mat3).transpose⁻¹ = (codeMat 190 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 355 : Mat3).transpose * (codeMat 190 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s48_source_le_transport :
    step103o279ActualSource48 ≤ actionW (codeMat 215) (codeMat 355) orbit14W := by
  apply step103o279_spanCodes_le_of_gens [262, 130, 68, 36, 16, 10, 1]
    (actionW (codeMat 215) (codeMat 355) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 126 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 126 (by decide)
    have hact : actionA (codeMat 215) (codeMat 355) (codeMat 126) = codeMat 262 := by
      unfold actionA
      rw [step103o279s48_QtInv]
      show (codeMat 215 : Mat3).transpose * codeMat 126 * (codeMat 190 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 9 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 9 (by decide)
    have hact : actionA (codeMat 215) (codeMat 355) (codeMat 9) = codeMat 130 := by
      unfold actionA
      rw [step103o279s48_QtInv]
      show (codeMat 215 : Mat3).transpose * codeMat 9 * (codeMat 190 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 245 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 245 (by decide)
    have hact : actionA (codeMat 215) (codeMat 355) (codeMat 245) = codeMat 68 := by
      unfold actionA
      rw [step103o279s48_QtInv]
      show (codeMat 215 : Mat3).transpose * codeMat 245 * (codeMat 190 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 215) (codeMat 355) (codeMat 384) = codeMat 36 := by
      unfold actionA
      rw [step103o279s48_QtInv]
      show (codeMat 215 : Mat3).transpose * codeMat 384 * (codeMat 190 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 215) (codeMat 355) (codeMat 8) = codeMat 16 := by
      unfold actionA
      rw [step103o279s48_QtInv]
      show (codeMat 215 : Mat3).transpose * codeMat 8 * (codeMat 190 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 215) (codeMat 355) (codeMat 96) = codeMat 10 := by
      unfold actionA
      rw [step103o279s48_QtInv]
      show (codeMat 215 : Mat3).transpose * codeMat 96 * (codeMat 190 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 215) (codeMat 355) (codeMat 360) = codeMat 1 := by
      unfold actionA
      rw [step103o279s48_QtInv]
      show (codeMat 215 : Mat3).transpose * codeMat 360 * (codeMat 190 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s48_qr :
    QuotientRankAtLeast step103o279ActualSource48 12 := by
  have hP : Invertible (codeMat 215 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 355 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 215) (codeMat 355) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 215) (codeMat 355) hP hQ orbit14W 12 orbit14_lb12
  exact quotientRankAtLeast_mono step103o279s48_source_le_transport hAct

-- Source 49: compressed row 49, orbit 14, action, lb 12
def step103o279ActualSource49 : Submodule F2 Mat3 := spanCodes [258, 132, 68, 32, 16, 10, 1]

private theorem step103o279_o279W_le_src49 : o279W ≤ spanCodes [258, 132, 68, 32, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s49_QtInv :
    (codeMat 481 : Mat3).transpose⁻¹ = (codeMat 185 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 481 : Mat3).transpose * (codeMat 185 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s49_source_le_transport :
    step103o279ActualSource49 ≤ actionW (codeMat 159) (codeMat 481) orbit14W := by
  apply step103o279_spanCodes_le_of_gens [258, 132, 68, 32, 16, 10, 1]
    (actionW (codeMat 159) (codeMat 481) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 278 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 278 (by decide)
    have hact : actionA (codeMat 159) (codeMat 481) (codeMat 278) = codeMat 258 := by
      unfold actionA
      rw [step103o279s49_QtInv]
      show (codeMat 159 : Mat3).transpose * codeMat 278 * (codeMat 185 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 404 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 404 (by decide)
    have hact : actionA (codeMat 159) (codeMat 481) (codeMat 404) = codeMat 132 := by
      unfold actionA
      rw [step103o279s49_QtInv]
      show (codeMat 159 : Mat3).transpose * codeMat 404 * (codeMat 185 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 413 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 413 (by decide)
    have hact : actionA (codeMat 159) (codeMat 481) (codeMat 413) = codeMat 68 := by
      unfold actionA
      rw [step103o279s49_QtInv]
      show (codeMat 159 : Mat3).transpose * codeMat 413 * (codeMat 185 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 159) (codeMat 481) (codeMat 384) = codeMat 32 := by
      unfold actionA
      rw [step103o279s49_QtInv]
      show (codeMat 159 : Mat3).transpose * codeMat 384 * (codeMat 185 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 159) (codeMat 481) (codeMat 256) = codeMat 16 := by
      unfold actionA
      rw [step103o279s49_QtInv]
      show (codeMat 159 : Mat3).transpose * codeMat 256 * (codeMat 185 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 159) (codeMat 481) (codeMat 96) = codeMat 10 := by
      unfold actionA
      rw [step103o279s49_QtInv]
      show (codeMat 159 : Mat3).transpose * codeMat 96 * (codeMat 185 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 159) (codeMat 481) (codeMat 360) = codeMat 1 := by
      unfold actionA
      rw [step103o279s49_QtInv]
      show (codeMat 159 : Mat3).transpose * codeMat 360 * (codeMat 185 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s49_qr :
    QuotientRankAtLeast step103o279ActualSource49 12 := by
  have hP : Invertible (codeMat 159 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 481 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 159) (codeMat 481) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 159) (codeMat 481) hP hQ orbit14W 12 orbit14_lb12
  exact quotientRankAtLeast_mono step103o279s49_source_le_transport hAct

-- Source 50: compressed row 50, orbit 3, action, lb 9
def step103o279ActualSource50 : Submodule F2 Mat3 := spanCodes [258, 130, 66, 34, 16, 10, 6, 1]

private theorem step103o279_o279W_le_src50 : o279W ≤ spanCodes [258, 130, 66, 34, 16, 10, 6, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 130, 66, 34, 16, 10, 6, 1] 68 (by decide)
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s50_QtInv :
    (codeMat 494 : Mat3).transpose⁻¹ = (codeMat 501 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 494 : Mat3).transpose * (codeMat 501 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s50_source_le_transport :
    step103o279ActualSource50 ≤ actionW (codeMat 84) (codeMat 494) flatW_3 := by
  apply step103o279_spanCodes_le_of_gens [258, 130, 66, 34, 16, 10, 6, 1]
    (actionW (codeMat 84) (codeMat 494) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 327 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 327 (by decide)
    have hact : actionA (codeMat 84) (codeMat 494) (codeMat 327) = codeMat 258 := by
      unfold actionA
      rw [step103o279s50_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 327 * (codeMat 501 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 325 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 325 (by decide)
    have hact : actionA (codeMat 84) (codeMat 494) (codeMat 325) = codeMat 130 := by
      unfold actionA
      rw [step103o279s50_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 325 * (codeMat 501 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 326 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 326 (by decide)
    have hact : actionA (codeMat 84) (codeMat 494) (codeMat 326) = codeMat 66 := by
      unfold actionA
      rw [step103o279s50_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 326 * (codeMat 501 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 376 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 376 (by decide)
    have hact : actionA (codeMat 84) (codeMat 494) (codeMat 376) = codeMat 34 := by
      unfold actionA
      rw [step103o279s50_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 376 * (codeMat 501 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 40 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 84) (codeMat 494) (codeMat 40) = codeMat 16 := by
      unfold actionA
      rw [step103o279s50_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 40 * (codeMat 501 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 368 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 368 (by decide)
    have hact : actionA (codeMat 84) (codeMat 494) (codeMat 368) = codeMat 10 := by
      unfold actionA
      rw [step103o279s50_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 368 * (codeMat 501 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 494) (codeMat 128) = codeMat 6 := by
      unfold actionA
      rw [step103o279s50_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 501 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 494) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step103o279s50_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 501 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s50_qr :
    QuotientRankAtLeast step103o279ActualSource50 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 494 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 494) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 494) hP hQ flatW_3 9 flatSeed_3
  exact quotientRankAtLeast_mono step103o279s50_source_le_transport hAct

-- Source 51: compressed row 51, orbit 65, action, lb 15
def step103o279ActualSource51 : Submodule F2 Mat3 := spanCodes [258, 164, 68, 16, 10, 1]

private theorem step103o279_o279W_le_src51 : o279W ≤ spanCodes [258, 164, 68, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s51_QtInv :
    (codeMat 419 : Mat3).transpose⁻¹ = (codeMat 183 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 419 : Mat3).transpose * (codeMat 183 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s51_source_le_transport :
    step103o279ActualSource51 ≤ actionW (codeMat 177) (codeMat 419) o65W := by
  apply step103o279_spanCodes_le_of_gens [258, 164, 68, 16, 10, 1]
    (actionW (codeMat 177) (codeMat 419) o65W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 437 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 437 (by decide)
    have hact : actionA (codeMat 177) (codeMat 419) (codeMat 437) = codeMat 258 := by
      unfold actionA
      rw [step103o279s51_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 437 * (codeMat 183 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 238 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 238 (by decide)
    have hact : actionA (codeMat 177) (codeMat 419) (codeMat 238) = codeMat 164 := by
      unfold actionA
      rw [step103o279s51_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 238 * (codeMat 183 : Mat3).transpose = codeMat 164
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 78 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 78 (by decide)
    have hact : actionA (codeMat 177) (codeMat 419) (codeMat 78) = codeMat 68 := by
      unfold actionA
      rw [step103o279s51_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 78 * (codeMat 183 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 320 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 320 (by decide)
    have hact : actionA (codeMat 177) (codeMat 419) (codeMat 320) = codeMat 16 := by
      unfold actionA
      rw [step103o279s51_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 320 * (codeMat 183 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 69 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 69 (by decide)
    have hact : actionA (codeMat 177) (codeMat 419) (codeMat 69) = codeMat 10 := by
      unfold actionA
      rw [step103o279s51_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 69 * (codeMat 183 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 419) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step103o279s51_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * (codeMat 183 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s51_qr :
    QuotientRankAtLeast step103o279ActualSource51 15 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 419 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 419) o65W) 15 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 419) hP hQ o65W 15 step99_orbit65_lb15_unconditional
  exact quotientRankAtLeast_mono step103o279s51_source_le_transport hAct

-- Source 52: compressed row 52, orbit 3, action, lb 9
def step103o279ActualSource52 : Submodule F2 Mat3 := spanCodes [256, 128, 66, 34, 16, 10, 6, 1]

private theorem step103o279_o279W_le_src52 : o279W ≤ spanCodes [256, 128, 66, 34, 16, 10, 6, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 66, 34, 16, 10, 6, 1] 68 (by decide)
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s52_QtInv :
    (codeMat 110 : Mat3).transpose⁻¹ = (codeMat 444 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 110 : Mat3).transpose * (codeMat 444 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s52_source_le_transport :
    step103o279ActualSource52 ≤ actionW (codeMat 84) (codeMat 110) flatW_3 := by
  apply step103o279_spanCodes_le_of_gens [256, 128, 66, 34, 16, 10, 6, 1]
    (actionW (codeMat 84) (codeMat 110) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 3 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 84) (codeMat 110) (codeMat 3) = codeMat 256 := by
      unfold actionA
      rw [step103o279s52_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 3 * (codeMat 444 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 110) (codeMat 1) = codeMat 128 := by
      unfold actionA
      rw [step103o279s52_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 444 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 70 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 70 (by decide)
    have hact : actionA (codeMat 84) (codeMat 110) (codeMat 70) = codeMat 66 := by
      unfold actionA
      rw [step103o279s52_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 70 * (codeMat 444 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 88 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 88 (by decide)
    have hact : actionA (codeMat 84) (codeMat 110) (codeMat 88) = codeMat 34 := by
      unfold actionA
      rw [step103o279s52_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 88 * (codeMat 444 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 110) (codeMat 8) = codeMat 16 := by
      unfold actionA
      rw [step103o279s52_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 444 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 112 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 112 (by decide)
    have hact : actionA (codeMat 84) (codeMat 110) (codeMat 112) = codeMat 10 := by
      unfold actionA
      rw [step103o279s52_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 112 * (codeMat 444 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 110) (codeMat 128) = codeMat 6 := by
      unfold actionA
      rw [step103o279s52_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 444 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 110) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step103o279s52_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 444 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s52_qr :
    QuotientRankAtLeast step103o279ActualSource52 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 110 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 110) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 110) hP hQ flatW_3 9 flatSeed_3
  exact quotientRankAtLeast_mono step103o279s52_source_le_transport hAct

-- Source 53: compressed row 53, orbit 14, action, lb 12
def step103o279ActualSource53 : Submodule F2 Mat3 := spanCodes [256, 128, 68, 36, 16, 10, 1]

private theorem step103o279_o279W_le_src53 : o279W ≤ spanCodes [256, 128, 68, 36, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s53_QtInv :
    (codeMat 99 : Mat3).transpose⁻¹ = (codeMat 172 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 99 : Mat3).transpose * (codeMat 172 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s53_source_le_transport :
    step103o279ActualSource53 ≤ actionW (codeMat 212) (codeMat 99) orbit14W := by
  apply step103o279_spanCodes_le_of_gens [256, 128, 68, 36, 16, 10, 1]
    (actionW (codeMat 212) (codeMat 99) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 212) (codeMat 99) (codeMat 2) = codeMat 256 := by
      unfold actionA
      rw [step103o279s53_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 2 * (codeMat 172 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 212) (codeMat 99) (codeMat 1) = codeMat 128 := by
      unfold actionA
      rw [step103o279s53_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 1 * (codeMat 172 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 149 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 149 (by decide)
    have hact : actionA (codeMat 212) (codeMat 99) (codeMat 149) = codeMat 68 := by
      unfold actionA
      rw [step103o279s53_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 149 * (codeMat 172 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 212) (codeMat 99) (codeMat 128) = codeMat 36 := by
      unfold actionA
      rw [step103o279s53_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 128 * (codeMat 172 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 212) (codeMat 99) (codeMat 8) = codeMat 16 := by
      unfold actionA
      rw [step103o279s53_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 8 * (codeMat 172 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 212) (codeMat 99) (codeMat 96) = codeMat 10 := by
      unfold actionA
      rw [step103o279s53_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 96 * (codeMat 172 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 212) (codeMat 99) (codeMat 360) = codeMat 1 := by
      unfold actionA
      rw [step103o279s53_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 360 * (codeMat 172 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s53_qr :
    QuotientRankAtLeast step103o279ActualSource53 12 := by
  have hP : Invertible (codeMat 212 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 99 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 212) (codeMat 99) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 212) (codeMat 99) hP hQ orbit14W 12 orbit14_lb12
  exact quotientRankAtLeast_mono step103o279s53_source_le_transport hAct

-- Source 54: compressed row 54, orbit 65, action, lb 15
def step103o279ActualSource54 : Submodule F2 Mat3 := spanCodes [294, 162, 68, 16, 10, 1]

private theorem step103o279_o279W_le_src54 : o279W ≤ spanCodes [294, 162, 68, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s54_QtInv :
    (codeMat 298 : Mat3).transpose⁻¹ = (codeMat 270 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 298 : Mat3).transpose * (codeMat 270 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s54_source_le_transport :
    step103o279ActualSource54 ≤ actionW (codeMat 266) (codeMat 298) o65W := by
  apply step103o279_spanCodes_le_of_gens [294, 162, 68, 16, 10, 1]
    (actionW (codeMat 266) (codeMat 298) o65W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 446 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 446 (by decide)
    have hact : actionA (codeMat 266) (codeMat 298) (codeMat 446) = codeMat 294 := by
      unfold actionA
      rw [step103o279s54_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 446 * (codeMat 270 : Mat3).transpose = codeMat 294
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 78 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 78 (by decide)
    have hact : actionA (codeMat 266) (codeMat 298) (codeMat 78) = codeMat 162 := by
      unfold actionA
      rw [step103o279s54_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 78 * (codeMat 270 : Mat3).transpose = codeMat 162
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 176 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 176 (by decide)
    have hact : actionA (codeMat 266) (codeMat 298) (codeMat 176) = codeMat 68 := by
      unfold actionA
      rw [step103o279s54_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 176 * (codeMat 270 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 298) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step103o279s54_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 270 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 10 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 266) (codeMat 298) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step103o279s54_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 10 * (codeMat 270 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 298) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step103o279s54_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 270 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s54_qr :
    QuotientRankAtLeast step103o279ActualSource54 15 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 298 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 298) o65W) 15 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 298) hP hQ o65W 15 step99_orbit65_lb15_unconditional
  exact quotientRankAtLeast_mono step103o279s54_source_le_transport hAct

-- Source 55: compressed row 55, orbit 65, action, lb 15
def step103o279ActualSource55 : Submodule F2 Mat3 := spanCodes [294, 160, 68, 16, 10, 1]

private theorem step103o279_o279W_le_src55 : o279W ≤ spanCodes [294, 160, 68, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s55_QtInv :
    (codeMat 314 : Mat3).transpose⁻¹ = (codeMat 271 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 314 : Mat3).transpose * (codeMat 271 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s55_source_le_transport :
    step103o279ActualSource55 ≤ actionW (codeMat 331) (codeMat 314) o65W := by
  apply step103o279_spanCodes_le_of_gens [294, 160, 68, 16, 10, 1]
    (actionW (codeMat 331) (codeMat 314) o65W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 430 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 430 (by decide)
    have hact : actionA (codeMat 331) (codeMat 314) (codeMat 430) = codeMat 294 := by
      unfold actionA
      rw [step103o279s55_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 430 * (codeMat 271 : Mat3).transpose = codeMat 294
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 238 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 238 (by decide)
    have hact : actionA (codeMat 331) (codeMat 314) (codeMat 238) = codeMat 160 := by
      unfold actionA
      rw [step103o279s55_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 238 * (codeMat 271 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 160 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 331) (codeMat 314) (codeMat 160) = codeMat 68 := by
      unfold actionA
      rw [step103o279s55_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 160 * (codeMat 271 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 27 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 27 (by decide)
    have hact : actionA (codeMat 331) (codeMat 314) (codeMat 27) = codeMat 16 := by
      unfold actionA
      rw [step103o279s55_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 27 * (codeMat 271 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 10 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 331) (codeMat 314) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step103o279s55_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 10 * (codeMat 271 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 331) (codeMat 314) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step103o279s55_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 16 * (codeMat 271 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s55_qr :
    QuotientRankAtLeast step103o279ActualSource55 15 := by
  have hP : Invertible (codeMat 331 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 314 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 331) (codeMat 314) o65W) 15 :=
    @quotientRankAtLeast_action (codeMat 331) (codeMat 314) hP hQ o65W 15 step99_orbit65_lb15_unconditional
  exact quotientRankAtLeast_mono step103o279s55_source_le_transport hAct

-- Source 56: compressed row 56, orbit 14, action, lb 12
def step103o279ActualSource56 : Submodule F2 Mat3 := spanCodes [256, 130, 68, 38, 16, 10, 1]

private theorem step103o279_o279W_le_src56 : o279W ≤ spanCodes [256, 130, 68, 38, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s56_QtInv :
    (codeMat 359 : Mat3).transpose⁻¹ = (codeMat 174 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 359 : Mat3).transpose * (codeMat 174 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s56_source_le_transport :
    step103o279ActualSource56 ≤ actionW (codeMat 213) (codeMat 359) orbit14W := by
  apply step103o279_spanCodes_le_of_gens [256, 130, 68, 38, 16, 10, 1]
    (actionW (codeMat 213) (codeMat 359) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 511 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 511 (by decide)
    have hact : actionA (codeMat 213) (codeMat 359) (codeMat 511) = codeMat 256 := by
      unfold actionA
      rw [step103o279s56_QtInv]
      show (codeMat 213 : Mat3).transpose * codeMat 511 * (codeMat 174 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 213) (codeMat 359) (codeMat 1) = codeMat 130 := by
      unfold actionA
      rw [step103o279s56_QtInv]
      show (codeMat 213 : Mat3).transpose * codeMat 1 * (codeMat 174 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 149 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 149 (by decide)
    have hact : actionA (codeMat 213) (codeMat 359) (codeMat 149) = codeMat 68 := by
      unfold actionA
      rw [step103o279s56_QtInv]
      show (codeMat 213 : Mat3).transpose * codeMat 149 * (codeMat 174 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 392 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 392 (by decide)
    have hact : actionA (codeMat 213) (codeMat 359) (codeMat 392) = codeMat 38 := by
      unfold actionA
      rw [step103o279s56_QtInv]
      show (codeMat 213 : Mat3).transpose * codeMat 392 * (codeMat 174 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 213) (codeMat 359) (codeMat 8) = codeMat 16 := by
      unfold actionA
      rw [step103o279s56_QtInv]
      show (codeMat 213 : Mat3).transpose * codeMat 8 * (codeMat 174 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 213) (codeMat 359) (codeMat 96) = codeMat 10 := by
      unfold actionA
      rw [step103o279s56_QtInv]
      show (codeMat 213 : Mat3).transpose * codeMat 96 * (codeMat 174 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 213) (codeMat 359) (codeMat 360) = codeMat 1 := by
      unfold actionA
      rw [step103o279s56_QtInv]
      show (codeMat 213 : Mat3).transpose * codeMat 360 * (codeMat 174 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s56_qr :
    QuotientRankAtLeast step103o279ActualSource56 12 := by
  have hP : Invertible (codeMat 213 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 359 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 213) (codeMat 359) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 213) (codeMat 359) hP hQ orbit14W 12 orbit14_lb12
  exact quotientRankAtLeast_mono step103o279s56_source_le_transport hAct

-- Source 57: compressed row 57, orbit 14, action, lb 12
def step103o279ActualSource57 : Submodule F2 Mat3 := spanCodes [258, 128, 68, 36, 16, 10, 1]

private theorem step103o279_o279W_le_src57 : o279W ≤ spanCodes [258, 128, 68, 36, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s57_QtInv :
    (codeMat 355 : Mat3).transpose⁻¹ = (codeMat 190 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 355 : Mat3).transpose * (codeMat 190 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s57_source_le_transport :
    step103o279ActualSource57 ≤ actionW (codeMat 214) (codeMat 355) orbit14W := by
  apply step103o279_spanCodes_le_of_gens [258, 128, 68, 36, 16, 10, 1]
    (actionW (codeMat 214) (codeMat 355) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 126 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 126 (by decide)
    have hact : actionA (codeMat 214) (codeMat 355) (codeMat 126) = codeMat 258 := by
      unfold actionA
      rw [step103o279s57_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 126 * (codeMat 190 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 9 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 9 (by decide)
    have hact : actionA (codeMat 214) (codeMat 355) (codeMat 9) = codeMat 128 := by
      unfold actionA
      rw [step103o279s57_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 9 * (codeMat 190 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 413 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 413 (by decide)
    have hact : actionA (codeMat 214) (codeMat 355) (codeMat 413) = codeMat 68 := by
      unfold actionA
      rw [step103o279s57_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 413 * (codeMat 190 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 214) (codeMat 355) (codeMat 384) = codeMat 36 := by
      unfold actionA
      rw [step103o279s57_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 384 * (codeMat 190 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 214) (codeMat 355) (codeMat 8) = codeMat 16 := by
      unfold actionA
      rw [step103o279s57_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 8 * (codeMat 190 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 214) (codeMat 355) (codeMat 96) = codeMat 10 := by
      unfold actionA
      rw [step103o279s57_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 96 * (codeMat 190 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 214) (codeMat 355) (codeMat 360) = codeMat 1 := by
      unfold actionA
      rw [step103o279s57_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 360 * (codeMat 190 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s57_qr :
    QuotientRankAtLeast step103o279ActualSource57 12 := by
  have hP : Invertible (codeMat 214 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 355 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 214) (codeMat 355) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 214) (codeMat 355) hP hQ orbit14W 12 orbit14_lb12
  exact quotientRankAtLeast_mono step103o279s57_source_le_transport hAct

-- Source 58: compressed row 58, orbit 10, action, lb 12
def step103o279ActualSource58 : Submodule F2 Mat3 := spanCodes [292, 164, 68, 16, 8, 2, 1]

private theorem step103o279_o279W_le_src58 : o279W ≤ spanCodes [292, 164, 68, 16, 8, 2, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [292, 164, 68, 16, 8, 2, 1] 10 (by decide)
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s58_QtInv :
    (codeMat 318 : Mat3).transpose⁻¹ = (codeMat 299 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 318 : Mat3).transpose * (codeMat 299 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s58_source_le_transport :
    step103o279ActualSource58 ≤ actionW (codeMat 266) (codeMat 318) orbit10W := by
  apply step103o279_spanCodes_le_of_gens [292, 164, 68, 16, 8, 2, 1]
    (actionW (codeMat 266) (codeMat 318) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 511 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 511 (by decide)
    have hact : actionA (codeMat 266) (codeMat 318) (codeMat 511) = codeMat 292 := by
      unfold actionA
      rw [step103o279s58_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 511 * (codeMat 299 : Mat3).transpose = codeMat 292
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 255 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 255 (by decide)
    have hact : actionA (codeMat 266) (codeMat 318) (codeMat 255) = codeMat 164 := by
      unfold actionA
      rw [step103o279s58_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 255 * (codeMat 299 : Mat3).transpose = codeMat 164
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 184 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 184 (by decide)
    have hact : actionA (codeMat 266) (codeMat 318) (codeMat 184) = codeMat 68 := by
      unfold actionA
      rw [step103o279s58_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 184 * (codeMat 299 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 3 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 3 (by decide)
    have hact : actionA (codeMat 266) (codeMat 318) (codeMat 3) = codeMat 16 := by
      unfold actionA
      rw [step103o279s58_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 3 * (codeMat 299 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 318) (codeMat 2) = codeMat 8 := by
      unfold actionA
      rw [step103o279s58_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 299 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 24 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide)
    have hact : actionA (codeMat 266) (codeMat 318) (codeMat 24) = codeMat 2 := by
      unfold actionA
      rw [step103o279s58_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 24 * (codeMat 299 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 318) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step103o279s58_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 299 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s58_qr :
    QuotientRankAtLeast step103o279ActualSource58 12 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 318 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 318) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 318) hP hQ orbit10W 12 orbit10_lb12
  exact quotientRankAtLeast_mono step103o279s58_source_le_transport hAct

-- Source 59: compressed row 59, orbit 14, action, lb 12
def step103o279ActualSource59 : Submodule F2 Mat3 := spanCodes [288, 162, 66, 16, 10, 6, 1]

private theorem step103o279_o279W_le_src59 : o279W ≤ spanCodes [288, 162, 66, 16, 10, 6, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 162, 66, 16, 10, 6, 1] 68 (by decide)
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s59_QtInv :
    (codeMat 426 : Mat3).transpose⁻¹ = (codeMat 335 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 426 : Mat3).transpose * (codeMat 335 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s59_source_le_transport :
    step103o279ActualSource59 ≤ actionW (codeMat 417) (codeMat 426) orbit14W := by
  apply step103o279_spanCodes_le_of_gens [288, 162, 66, 16, 10, 6, 1]
    (actionW (codeMat 417) (codeMat 426) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 417) (codeMat 426) (codeMat 384) = codeMat 288 := by
      unfold actionA
      rw [step103o279s59_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 384 * (codeMat 335 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 413 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 413 (by decide)
    have hact : actionA (codeMat 417) (codeMat 426) (codeMat 413) = codeMat 162 := by
      unfold actionA
      rw [step103o279s59_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 413 * (codeMat 335 : Mat3).transpose = codeMat 162
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 21 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 21 (by decide)
    have hact : actionA (codeMat 417) (codeMat 426) (codeMat 21) = codeMat 66 := by
      unfold actionA
      rw [step103o279s59_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 21 * (codeMat 335 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 417) (codeMat 426) (codeMat 360) = codeMat 16 := by
      unfold actionA
      rw [step103o279s59_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 360 * (codeMat 335 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 149 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 149 (by decide)
    have hact : actionA (codeMat 417) (codeMat 426) (codeMat 149) = codeMat 10 := by
      unfold actionA
      rw [step103o279s59_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 149 * (codeMat 335 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 417) (codeMat 426) (codeMat 3) = codeMat 6 := by
      unfold actionA
      rw [step103o279s59_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 3 * (codeMat 335 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 417) (codeMat 426) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step103o279s59_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 2 * (codeMat 335 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s59_qr :
    QuotientRankAtLeast step103o279ActualSource59 12 := by
  have hP : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 426 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 417) (codeMat 426) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 417) (codeMat 426) hP hQ orbit14W 12 orbit14_lb12
  exact quotientRankAtLeast_mono step103o279s59_source_le_transport hAct

-- Source 60: compressed row 60, orbit 14, action, lb 12
def step103o279ActualSource60 : Submodule F2 Mat3 := spanCodes [262, 132, 68, 34, 16, 10, 1]

private theorem step103o279_o279W_le_src60 : o279W ≤ spanCodes [262, 132, 68, 34, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s60_QtInv :
    (codeMat 229 : Mat3).transpose⁻¹ = (codeMat 187 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 229 : Mat3).transpose * (codeMat 187 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s60_source_le_transport :
    step103o279ActualSource60 ≤ actionW (codeMat 159) (codeMat 229) orbit14W := by
  apply step103o279_spanCodes_le_of_gens [262, 132, 68, 34, 16, 10, 1]
    (actionW (codeMat 159) (codeMat 229) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 483 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 483 (by decide)
    have hact : actionA (codeMat 159) (codeMat 229) (codeMat 483) = codeMat 262 := by
      unfold actionA
      rw [step103o279s60_QtInv]
      show (codeMat 159 : Mat3).transpose * codeMat 483 * (codeMat 187 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 252 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 252 (by decide)
    have hact : actionA (codeMat 159) (codeMat 229) (codeMat 252) = codeMat 132 := by
      unfold actionA
      rw [step103o279s60_QtInv]
      show (codeMat 159 : Mat3).transpose * codeMat 252 * (codeMat 187 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 245 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 245 (by decide)
    have hact : actionA (codeMat 159) (codeMat 229) (codeMat 245) = codeMat 68 := by
      unfold actionA
      rw [step103o279s60_QtInv]
      show (codeMat 159 : Mat3).transpose * codeMat 245 * (codeMat 187 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 480 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 480 (by decide)
    have hact : actionA (codeMat 159) (codeMat 229) (codeMat 480) = codeMat 34 := by
      unfold actionA
      rw [step103o279s60_QtInv]
      show (codeMat 159 : Mat3).transpose * codeMat 480 * (codeMat 187 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 159) (codeMat 229) (codeMat 256) = codeMat 16 := by
      unfold actionA
      rw [step103o279s60_QtInv]
      show (codeMat 159 : Mat3).transpose * codeMat 256 * (codeMat 187 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 159) (codeMat 229) (codeMat 96) = codeMat 10 := by
      unfold actionA
      rw [step103o279s60_QtInv]
      show (codeMat 159 : Mat3).transpose * codeMat 96 * (codeMat 187 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 159) (codeMat 229) (codeMat 360) = codeMat 1 := by
      unfold actionA
      rw [step103o279s60_QtInv]
      show (codeMat 159 : Mat3).transpose * codeMat 360 * (codeMat 187 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s60_qr :
    QuotientRankAtLeast step103o279ActualSource60 12 := by
  have hP : Invertible (codeMat 159 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 229 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 159) (codeMat 229) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 159) (codeMat 229) hP hQ orbit14W 12 orbit14_lb12
  exact quotientRankAtLeast_mono step103o279s60_source_le_transport hAct

-- Source 61: compressed row 61, orbit 14, action, lb 12
def step103o279ActualSource61 : Submodule F2 Mat3 := spanCodes [262, 134, 68, 32, 16, 10, 1]

private theorem step103o279_o279W_le_src61 : o279W ≤ spanCodes [262, 134, 68, 32, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s61_QtInv :
    (codeMat 481 : Mat3).transpose⁻¹ = (codeMat 185 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 481 : Mat3).transpose * (codeMat 185 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s61_source_le_transport :
    step103o279ActualSource61 ≤ actionW (codeMat 158) (codeMat 481) orbit14W := by
  apply step103o279_spanCodes_le_of_gens [262, 134, 68, 32, 16, 10, 1]
    (actionW (codeMat 158) (codeMat 481) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 278 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 278 (by decide)
    have hact : actionA (codeMat 158) (codeMat 481) (codeMat 278) = codeMat 262 := by
      unfold actionA
      rw [step103o279s61_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 278 * (codeMat 185 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 404 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 404 (by decide)
    have hact : actionA (codeMat 158) (codeMat 481) (codeMat 404) = codeMat 134 := by
      unfold actionA
      rw [step103o279s61_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 404 * (codeMat 185 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 245 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 245 (by decide)
    have hact : actionA (codeMat 158) (codeMat 481) (codeMat 245) = codeMat 68 := by
      unfold actionA
      rw [step103o279s61_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 245 * (codeMat 185 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 158) (codeMat 481) (codeMat 384) = codeMat 32 := by
      unfold actionA
      rw [step103o279s61_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 384 * (codeMat 185 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 158) (codeMat 481) (codeMat 256) = codeMat 16 := by
      unfold actionA
      rw [step103o279s61_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 256 * (codeMat 185 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 158) (codeMat 481) (codeMat 96) = codeMat 10 := by
      unfold actionA
      rw [step103o279s61_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 96 * (codeMat 185 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 158) (codeMat 481) (codeMat 360) = codeMat 1 := by
      unfold actionA
      rw [step103o279s61_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 360 * (codeMat 185 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s61_qr :
    QuotientRankAtLeast step103o279ActualSource61 12 := by
  have hP : Invertible (codeMat 158 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 481 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 158) (codeMat 481) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 158) (codeMat 481) hP hQ orbit14W 12 orbit14_lb12
  exact quotientRankAtLeast_mono step103o279s61_source_le_transport hAct

-- Source 62: compressed row 62, orbit 14, action, lb 12
def step103o279ActualSource62 : Submodule F2 Mat3 := spanCodes [260, 132, 68, 34, 16, 10, 1]

private theorem step103o279_o279W_le_src62 : o279W ≤ spanCodes [260, 132, 68, 34, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s62_QtInv :
    (codeMat 485 : Mat3).transpose⁻¹ = (codeMat 171 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 485 : Mat3).transpose * (codeMat 171 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s62_source_le_transport :
    step103o279ActualSource62 ≤ actionW (codeMat 156) (codeMat 485) orbit14W := by
  apply step103o279_spanCodes_le_of_gens [260, 132, 68, 34, 16, 10, 1]
    (actionW (codeMat 156) (codeMat 485) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 511 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 511 (by decide)
    have hact : actionA (codeMat 156) (codeMat 485) (codeMat 511) = codeMat 260 := by
      unfold actionA
      rw [step103o279s62_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 511 * (codeMat 171 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 508 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 508 (by decide)
    have hact : actionA (codeMat 156) (codeMat 485) (codeMat 508) = codeMat 132 := by
      unfold actionA
      rw [step103o279s62_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 508 * (codeMat 171 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 509 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 509 (by decide)
    have hact : actionA (codeMat 156) (codeMat 485) (codeMat 509) = codeMat 68 := by
      unfold actionA
      rw [step103o279s62_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 509 * (codeMat 171 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 224 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 224 (by decide)
    have hact : actionA (codeMat 156) (codeMat 485) (codeMat 224) = codeMat 34 := by
      unfold actionA
      rw [step103o279s62_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 224 * (codeMat 171 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 156) (codeMat 485) (codeMat 256) = codeMat 16 := by
      unfold actionA
      rw [step103o279s62_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 256 * (codeMat 171 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 156) (codeMat 485) (codeMat 96) = codeMat 10 := by
      unfold actionA
      rw [step103o279s62_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 96 * (codeMat 171 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 156) (codeMat 485) (codeMat 360) = codeMat 1 := by
      unfold actionA
      rw [step103o279s62_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 360 * (codeMat 171 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s62_qr :
    QuotientRankAtLeast step103o279ActualSource62 12 := by
  have hP : Invertible (codeMat 156 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 485 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 156) (codeMat 485) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 156) (codeMat 485) hP hQ orbit14W 12 orbit14_lb12
  exact quotientRankAtLeast_mono step103o279s62_source_le_transport hAct

-- Source 63: compressed row 63, orbit 14, action, lb 12
def step103o279ActualSource63 : Submodule F2 Mat3 := spanCodes [258, 130, 68, 38, 16, 10, 1]

private theorem step103o279_o279W_le_src63 : o279W ≤ spanCodes [258, 130, 68, 38, 16, 10, 1] := by
  unfold o279W
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact Submodule.subset_span ⟨68, by simp, rfl⟩
  · subst h1
    exact Submodule.subset_span ⟨16, by simp, rfl⟩
  · subst h2
    exact Submodule.subset_span ⟨10, by simp, rfl⟩
  · subst h3
    exact Submodule.subset_span ⟨1, by simp, rfl⟩

private theorem step103o279s63_QtInv :
    (codeMat 103 : Mat3).transpose⁻¹ = (codeMat 188 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 103 : Mat3).transpose * (codeMat 188 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step103o279s63_source_le_transport :
    step103o279ActualSource63 ≤ actionW (codeMat 215) (codeMat 103) orbit14W := by
  apply step103o279_spanCodes_le_of_gens [258, 130, 68, 38, 16, 10, 1]
    (actionW (codeMat 215) (codeMat 103) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 139 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 139 (by decide)
    have hact : actionA (codeMat 215) (codeMat 103) (codeMat 139) = codeMat 258 := by
      unfold actionA
      rw [step103o279s63_QtInv]
      show (codeMat 215 : Mat3).transpose * codeMat 139 * (codeMat 188 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 9 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 9 (by decide)
    have hact : actionA (codeMat 215) (codeMat 103) (codeMat 9) = codeMat 130 := by
      unfold actionA
      rw [step103o279s63_QtInv]
      show (codeMat 215 : Mat3).transpose * codeMat 9 * (codeMat 188 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 413 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 413 (by decide)
    have hact : actionA (codeMat 215) (codeMat 103) (codeMat 413) = codeMat 68 := by
      unfold actionA
      rw [step103o279s63_QtInv]
      show (codeMat 215 : Mat3).transpose * codeMat 413 * (codeMat 188 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 136 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 136 (by decide)
    have hact : actionA (codeMat 215) (codeMat 103) (codeMat 136) = codeMat 38 := by
      unfold actionA
      rw [step103o279s63_QtInv]
      show (codeMat 215 : Mat3).transpose * codeMat 136 * (codeMat 188 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 215) (codeMat 103) (codeMat 8) = codeMat 16 := by
      unfold actionA
      rw [step103o279s63_QtInv]
      show (codeMat 215 : Mat3).transpose * codeMat 8 * (codeMat 188 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 215) (codeMat 103) (codeMat 96) = codeMat 10 := by
      unfold actionA
      rw [step103o279s63_QtInv]
      show (codeMat 215 : Mat3).transpose * codeMat 96 * (codeMat 188 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 215) (codeMat 103) (codeMat 360) = codeMat 1 := by
      unfold actionA
      rw [step103o279s63_QtInv]
      show (codeMat 215 : Mat3).transpose * codeMat 360 * (codeMat 188 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step103o279_codeMat_mem_actionW_of_witness hw hact

private theorem step103o279s63_qr :
    QuotientRankAtLeast step103o279ActualSource63 12 := by
  have hP : Invertible (codeMat 215 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 103 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 215) (codeMat 103) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 215) (codeMat 103) hP hQ orbit14W 12 orbit14_lb12
  exact quotientRankAtLeast_mono step103o279s63_source_le_transport hAct

-- Per-compressed-row theorem aliases with W-containment and QR facts.
theorem step103_o279_row0_W_le_source : o279W ≤ step103o279ActualSource0 :=
  step103o279_o279W_le_src0
theorem step103_o279_row0_qr : QuotientRankAtLeast step103o279ActualSource0 16 :=
  step103o279s0_qr

theorem step103_o279_row1_W_le_source : o279W ≤ step103o279ActualSource1 :=
  step103o279_o279W_le_src1
theorem step103_o279_row1_qr : QuotientRankAtLeast step103o279ActualSource1 15 :=
  step103o279s1_qr

theorem step103_o279_row2_W_le_source : o279W ≤ step103o279ActualSource2 :=
  step103o279_o279W_le_src2
theorem step103_o279_row2_qr : QuotientRankAtLeast step103o279ActualSource2 15 :=
  step103o279s2_qr

theorem step103_o279_row3_W_le_source : o279W ≤ step103o279ActualSource3 :=
  step103o279_o279W_le_src3
theorem step103_o279_row3_qr : QuotientRankAtLeast step103o279ActualSource3 15 :=
  step103o279s3_qr

theorem step103_o279_row4_W_le_source : o279W ≤ step103o279ActualSource4 :=
  step103o279_o279W_le_src4
theorem step103_o279_row4_qr : QuotientRankAtLeast step103o279ActualSource4 15 :=
  step103o279s4_qr

theorem step103_o279_row5_W_le_source : o279W ≤ step103o279ActualSource5 :=
  step103o279_o279W_le_src5
theorem step103_o279_row5_qr : QuotientRankAtLeast step103o279ActualSource5 15 :=
  step103o279s5_qr

theorem step103_o279_row6_W_le_source : o279W ≤ step103o279ActualSource6 :=
  step103o279_o279W_le_src6
theorem step103_o279_row6_qr : QuotientRankAtLeast step103o279ActualSource6 15 :=
  step103o279s6_qr

theorem step103_o279_row7_W_le_source : o279W ≤ step103o279ActualSource7 :=
  step103o279_o279W_le_src7
theorem step103_o279_row7_qr : QuotientRankAtLeast step103o279ActualSource7 15 :=
  step103o279s7_qr

theorem step103_o279_row8_W_le_source : o279W ≤ step103o279ActualSource8 :=
  step103o279_o279W_le_src8
theorem step103_o279_row8_qr : QuotientRankAtLeast step103o279ActualSource8 15 :=
  step103o279s8_qr

theorem step103_o279_row9_W_le_source : o279W ≤ step103o279ActualSource9 :=
  step103o279_o279W_le_src9
theorem step103_o279_row9_qr : QuotientRankAtLeast step103o279ActualSource9 15 :=
  step103o279s9_qr

theorem step103_o279_row10_W_le_source : o279W ≤ step103o279ActualSource10 :=
  step103o279_o279W_le_src10
theorem step103_o279_row10_qr : QuotientRankAtLeast step103o279ActualSource10 12 :=
  step103o279s10_qr

theorem step103_o279_row11_W_le_source : o279W ≤ step103o279ActualSource11 :=
  step103o279_o279W_le_src11
theorem step103_o279_row11_qr : QuotientRankAtLeast step103o279ActualSource11 12 :=
  step103o279s11_qr

theorem step103_o279_row12_W_le_source : o279W ≤ step103o279ActualSource12 :=
  step103o279_o279W_le_src12
theorem step103_o279_row12_qr : QuotientRankAtLeast step103o279ActualSource12 12 :=
  step103o279s12_qr

theorem step103_o279_row13_W_le_source : o279W ≤ step103o279ActualSource13 :=
  step103o279_o279W_le_src13
theorem step103_o279_row13_qr : QuotientRankAtLeast step103o279ActualSource13 12 :=
  step103o279s13_qr

theorem step103_o279_row14_W_le_source : o279W ≤ step103o279ActualSource14 :=
  step103o279_o279W_le_src14
theorem step103_o279_row14_qr : QuotientRankAtLeast step103o279ActualSource14 12 :=
  step103o279s14_qr

theorem step103_o279_row15_W_le_source : o279W ≤ step103o279ActualSource15 :=
  step103o279_o279W_le_src15
theorem step103_o279_row15_qr : QuotientRankAtLeast step103o279ActualSource15 12 :=
  step103o279s15_qr

theorem step103_o279_row16_W_le_source : o279W ≤ step103o279ActualSource16 :=
  step103o279_o279W_le_src16
theorem step103_o279_row16_qr : QuotientRankAtLeast step103o279ActualSource16 12 :=
  step103o279s16_qr

theorem step103_o279_row17_W_le_source : o279W ≤ step103o279ActualSource17 :=
  step103o279_o279W_le_src17
theorem step103_o279_row17_qr : QuotientRankAtLeast step103o279ActualSource17 12 :=
  step103o279s17_qr

theorem step103_o279_row18_W_le_source : o279W ≤ step103o279ActualSource18 :=
  step103o279_o279W_le_src18
theorem step103_o279_row18_qr : QuotientRankAtLeast step103o279ActualSource18 12 :=
  step103o279s18_qr

theorem step103_o279_row19_W_le_source : o279W ≤ step103o279ActualSource19 :=
  step103o279_o279W_le_src19
theorem step103_o279_row19_qr : QuotientRankAtLeast step103o279ActualSource19 12 :=
  step103o279s19_qr

theorem step103_o279_row20_W_le_source : o279W ≤ step103o279ActualSource20 :=
  step103o279_o279W_le_src20
theorem step103_o279_row20_qr : QuotientRankAtLeast step103o279ActualSource20 12 :=
  step103o279s20_qr

theorem step103_o279_row21_W_le_source : o279W ≤ step103o279ActualSource21 :=
  step103o279_o279W_le_src21
theorem step103_o279_row21_qr : QuotientRankAtLeast step103o279ActualSource21 16 :=
  step103o279s21_qr

theorem step103_o279_row22_W_le_source : o279W ≤ step103o279ActualSource22 :=
  step103o279_o279W_le_src22
theorem step103_o279_row22_qr : QuotientRankAtLeast step103o279ActualSource22 16 :=
  step103o279s22_qr

theorem step103_o279_row23_W_le_source : o279W ≤ step103o279ActualSource23 :=
  step103o279_o279W_le_src23
theorem step103_o279_row23_qr : QuotientRankAtLeast step103o279ActualSource23 15 :=
  step103o279s23_qr

theorem step103_o279_row24_W_le_source : o279W ≤ step103o279ActualSource24 :=
  step103o279_o279W_le_src24
theorem step103_o279_row24_qr : QuotientRankAtLeast step103o279ActualSource24 12 :=
  step103o279s24_qr

theorem step103_o279_row25_W_le_source : o279W ≤ step103o279ActualSource25 :=
  step103o279_o279W_le_src25
theorem step103_o279_row25_qr : QuotientRankAtLeast step103o279ActualSource25 12 :=
  step103o279s25_qr

theorem step103_o279_row26_W_le_source : o279W ≤ step103o279ActualSource26 :=
  step103o279_o279W_le_src26
theorem step103_o279_row26_qr : QuotientRankAtLeast step103o279ActualSource26 12 :=
  step103o279s26_qr

theorem step103_o279_row27_W_le_source : o279W ≤ step103o279ActualSource27 :=
  step103o279_o279W_le_src27
theorem step103_o279_row27_qr : QuotientRankAtLeast step103o279ActualSource27 12 :=
  step103o279s27_qr

theorem step103_o279_row28_W_le_source : o279W ≤ step103o279ActualSource28 :=
  step103o279_o279W_le_src28
theorem step103_o279_row28_qr : QuotientRankAtLeast step103o279ActualSource28 12 :=
  step103o279s28_qr

theorem step103_o279_row29_W_le_source : o279W ≤ step103o279ActualSource29 :=
  step103o279_o279W_le_src29
theorem step103_o279_row29_qr : QuotientRankAtLeast step103o279ActualSource29 9 :=
  step103o279s29_qr

theorem step103_o279_row30_W_le_source : o279W ≤ step103o279ActualSource30 :=
  step103o279_o279W_le_src30
theorem step103_o279_row30_qr : QuotientRankAtLeast step103o279ActualSource30 9 :=
  step103o279s30_qr

theorem step103_o279_row31_W_le_source : o279W ≤ step103o279ActualSource31 :=
  step103o279_o279W_le_src31
theorem step103_o279_row31_qr : QuotientRankAtLeast step103o279ActualSource31 12 :=
  step103o279s31_qr

theorem step103_o279_row32_W_le_source : o279W ≤ step103o279ActualSource32 :=
  step103o279_o279W_le_src32
theorem step103_o279_row32_qr : QuotientRankAtLeast step103o279ActualSource32 12 :=
  step103o279s32_qr

theorem step103_o279_row33_W_le_source : o279W ≤ step103o279ActualSource33 :=
  step103o279_o279W_le_src33
theorem step103_o279_row33_qr : QuotientRankAtLeast step103o279ActualSource33 9 :=
  step103o279s33_qr

theorem step103_o279_row34_W_le_source : o279W ≤ step103o279ActualSource34 :=
  step103o279_o279W_le_src34
theorem step103_o279_row34_qr : QuotientRankAtLeast step103o279ActualSource34 9 :=
  step103o279s34_qr

theorem step103_o279_row35_W_le_source : o279W ≤ step103o279ActualSource35 :=
  step103o279_o279W_le_src35
theorem step103_o279_row35_qr : QuotientRankAtLeast step103o279ActualSource35 16 :=
  step103o279s35_qr

theorem step103_o279_row36_W_le_source : o279W ≤ step103o279ActualSource36 :=
  step103o279_o279W_le_src36
theorem step103_o279_row36_qr : QuotientRankAtLeast step103o279ActualSource36 15 :=
  step103o279s36_qr

theorem step103_o279_row37_W_le_source : o279W ≤ step103o279ActualSource37 :=
  step103o279_o279W_le_src37
theorem step103_o279_row37_qr : QuotientRankAtLeast step103o279ActualSource37 15 :=
  step103o279s37_qr

theorem step103_o279_row38_W_le_source : o279W ≤ step103o279ActualSource38 :=
  step103o279_o279W_le_src38
theorem step103_o279_row38_qr : QuotientRankAtLeast step103o279ActualSource38 12 :=
  step103o279s38_qr

theorem step103_o279_row39_W_le_source : o279W ≤ step103o279ActualSource39 :=
  step103o279_o279W_le_src39
theorem step103_o279_row39_qr : QuotientRankAtLeast step103o279ActualSource39 12 :=
  step103o279s39_qr

theorem step103_o279_row40_W_le_source : o279W ≤ step103o279ActualSource40 :=
  step103o279_o279W_le_src40
theorem step103_o279_row40_qr : QuotientRankAtLeast step103o279ActualSource40 12 :=
  step103o279s40_qr

theorem step103_o279_row41_W_le_source : o279W ≤ step103o279ActualSource41 :=
  step103o279_o279W_le_src41
theorem step103_o279_row41_qr : QuotientRankAtLeast step103o279ActualSource41 12 :=
  step103o279s41_qr

theorem step103_o279_row42_W_le_source : o279W ≤ step103o279ActualSource42 :=
  step103o279_o279W_le_src42
theorem step103_o279_row42_qr : QuotientRankAtLeast step103o279ActualSource42 9 :=
  step103o279s42_qr

theorem step103_o279_row43_W_le_source : o279W ≤ step103o279ActualSource43 :=
  step103o279_o279W_le_src43
theorem step103_o279_row43_qr : QuotientRankAtLeast step103o279ActualSource43 9 :=
  step103o279s43_qr

theorem step103_o279_row44_W_le_source : o279W ≤ step103o279ActualSource44 :=
  step103o279_o279W_le_src44
theorem step103_o279_row44_qr : QuotientRankAtLeast step103o279ActualSource44 12 :=
  step103o279s44_qr

theorem step103_o279_row45_W_le_source : o279W ≤ step103o279ActualSource45 :=
  step103o279_o279W_le_src45
theorem step103_o279_row45_qr : QuotientRankAtLeast step103o279ActualSource45 15 :=
  step103o279s45_qr

theorem step103_o279_row46_W_le_source : o279W ≤ step103o279ActualSource46 :=
  step103o279_o279W_le_src46
theorem step103_o279_row46_qr : QuotientRankAtLeast step103o279ActualSource46 15 :=
  step103o279s46_qr

theorem step103_o279_row47_W_le_source : o279W ≤ step103o279ActualSource47 :=
  step103o279_o279W_le_src47
theorem step103_o279_row47_qr : QuotientRankAtLeast step103o279ActualSource47 12 :=
  step103o279s47_qr

theorem step103_o279_row48_W_le_source : o279W ≤ step103o279ActualSource48 :=
  step103o279_o279W_le_src48
theorem step103_o279_row48_qr : QuotientRankAtLeast step103o279ActualSource48 12 :=
  step103o279s48_qr

theorem step103_o279_row49_W_le_source : o279W ≤ step103o279ActualSource49 :=
  step103o279_o279W_le_src49
theorem step103_o279_row49_qr : QuotientRankAtLeast step103o279ActualSource49 12 :=
  step103o279s49_qr

theorem step103_o279_row50_W_le_source : o279W ≤ step103o279ActualSource50 :=
  step103o279_o279W_le_src50
theorem step103_o279_row50_qr : QuotientRankAtLeast step103o279ActualSource50 9 :=
  step103o279s50_qr

theorem step103_o279_row51_W_le_source : o279W ≤ step103o279ActualSource51 :=
  step103o279_o279W_le_src51
theorem step103_o279_row51_qr : QuotientRankAtLeast step103o279ActualSource51 15 :=
  step103o279s51_qr

theorem step103_o279_row52_W_le_source : o279W ≤ step103o279ActualSource52 :=
  step103o279_o279W_le_src52
theorem step103_o279_row52_qr : QuotientRankAtLeast step103o279ActualSource52 9 :=
  step103o279s52_qr

theorem step103_o279_row53_W_le_source : o279W ≤ step103o279ActualSource53 :=
  step103o279_o279W_le_src53
theorem step103_o279_row53_qr : QuotientRankAtLeast step103o279ActualSource53 12 :=
  step103o279s53_qr

theorem step103_o279_row54_W_le_source : o279W ≤ step103o279ActualSource54 :=
  step103o279_o279W_le_src54
theorem step103_o279_row54_qr : QuotientRankAtLeast step103o279ActualSource54 15 :=
  step103o279s54_qr

theorem step103_o279_row55_W_le_source : o279W ≤ step103o279ActualSource55 :=
  step103o279_o279W_le_src55
theorem step103_o279_row55_qr : QuotientRankAtLeast step103o279ActualSource55 15 :=
  step103o279s55_qr

theorem step103_o279_row56_W_le_source : o279W ≤ step103o279ActualSource56 :=
  step103o279_o279W_le_src56
theorem step103_o279_row56_qr : QuotientRankAtLeast step103o279ActualSource56 12 :=
  step103o279s56_qr

theorem step103_o279_row57_W_le_source : o279W ≤ step103o279ActualSource57 :=
  step103o279_o279W_le_src57
theorem step103_o279_row57_qr : QuotientRankAtLeast step103o279ActualSource57 12 :=
  step103o279s57_qr

theorem step103_o279_row58_W_le_source : o279W ≤ step103o279ActualSource58 :=
  step103o279_o279W_le_src58
theorem step103_o279_row58_qr : QuotientRankAtLeast step103o279ActualSource58 12 :=
  step103o279s58_qr

theorem step103_o279_row59_W_le_source : o279W ≤ step103o279ActualSource59 :=
  step103o279_o279W_le_src59
theorem step103_o279_row59_qr : QuotientRankAtLeast step103o279ActualSource59 12 :=
  step103o279s59_qr

theorem step103_o279_row60_W_le_source : o279W ≤ step103o279ActualSource60 :=
  step103o279_o279W_le_src60
theorem step103_o279_row60_qr : QuotientRankAtLeast step103o279ActualSource60 12 :=
  step103o279s60_qr

theorem step103_o279_row61_W_le_source : o279W ≤ step103o279ActualSource61 :=
  step103o279_o279W_le_src61
theorem step103_o279_row61_qr : QuotientRankAtLeast step103o279ActualSource61 12 :=
  step103o279s61_qr

theorem step103_o279_row62_W_le_source : o279W ≤ step103o279ActualSource62 :=
  step103o279_o279W_le_src62
theorem step103_o279_row62_qr : QuotientRankAtLeast step103o279ActualSource62 12 :=
  step103o279s62_qr

theorem step103_o279_row63_W_le_source : o279W ≤ step103o279ActualSource63 :=
  step103o279_o279W_le_src63
theorem step103_o279_row63_qr : QuotientRankAtLeast step103o279ActualSource63 12 :=
  step103o279s63_qr

end QiushiMatmul
