import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbit10FP
import QiushiOrbitTransport
import QiushiStep98Orbit231Consumer

set_option maxHeartbeats 800000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem step99o231_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step99o231MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step99o231_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step99o231MatrixCodeNat M) = M := by decide

lemma step99o231_codeMat_matrixCode (M : Mat3) :
    codeMat (step99o231MatrixCodeNat M) = M :=
  step99o231_codeMat_matrixCode_all M

private theorem step99o231_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step99o231_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

-- Source 0 (row 5): orbit 10, lb 12
def step99o231ActualSource0 : Submodule F2 Mat3 := spanCodes [256, 132, 96, 16, 8, 2, 1]

private theorem step99o231s0_sourceU_le :
    (o231SourceU ⟨0, by omega⟩) ≤ step99o231ActualSource0 := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 132, 96, 16, 8, 2, 1] (step99o231MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 132) ⊓ kerEvalFunc (codeMat 66 + codeMat 34)) at hM
    change (evalFunc (codeMat 132) M = 0 ∧ evalFunc (codeMat 66 + codeMat 34) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 132, 96, 16, 8, 2, 1] (step99o231MatrixCodeNat M) hbool
  rwa [step99o231_codeMat_matrixCode] at hspan

private theorem step99o231s0_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o231s0_targetSpan_le_action :
    step99o231ActualSource0 ≤ actionW (codeMat 266) (codeMat 273) orbit10W := by
  apply step99o231_spanCodes_le_of_gens [256, 132, 96, 16, 8, 2, 1]
    (actionW (codeMat 266) (codeMat 273) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 266) (codeMat 273) (codeMat 256) = codeMat 256 := by
      unfold actionA
      rw [step99o231s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 256 * (codeMat 273 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 266) (codeMat 273) (codeMat 160) = codeMat 132 := by
      unfold actionA
      rw [step99o231s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 160 * (codeMat 273 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 266) (codeMat 273) (codeMat 68) = codeMat 96 := by
      unfold actionA
      rw [step99o231s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 68 * (codeMat 273 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 273) (codeMat 2) = codeMat 16 := by
      unfold actionA
      rw [step99o231s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 273) (codeMat 1) = codeMat 8 := by
      unfold actionA
      rw [step99o231s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 273) (codeMat 16) = codeMat 2 := by
      unfold actionA
      rw [step99o231s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 273 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 273) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step99o231s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact

theorem step99o231s0Dispatch :
    QuotientRankAtLeast (o231SourceU ⟨0, by omega⟩) 12 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 273) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 273) hP hQ orbit10W 12 orbit10_lb12
  have hMono : QuotientRankAtLeast step99o231ActualSource0 12 :=
    quotientRankAtLeast_mono step99o231s0_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o231s0_sourceU_le hMono

-- Source 1 (row 12): orbit 10, lb 12
def step99o231ActualSource1 : Submodule F2 Mat3 := spanCodes [256, 136, 64, 34, 16, 4, 1]

private theorem step99o231s1_sourceU_le :
    (o231SourceU ⟨1, by omega⟩) ≤ step99o231ActualSource1 := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 136, 64, 34, 16, 4, 1] (step99o231MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 132 + codeMat 12) ⊓ kerEvalFunc (codeMat 34)) at hM
    change (evalFunc (codeMat 132 + codeMat 12) M = 0 ∧ evalFunc (codeMat 34) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 136, 64, 34, 16, 4, 1] (step99o231MatrixCodeNat M) hbool
  rwa [step99o231_codeMat_matrixCode] at hspan

private theorem step99o231s1_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o231s1_targetSpan_le_action :
    step99o231ActualSource1 ≤ actionW (codeMat 140) (codeMat 161) orbit10W := by
  apply step99o231_spanCodes_le_of_gens [256, 136, 64, 34, 16, 4, 1]
    (actionW (codeMat 140) (codeMat 161) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 2) = codeMat 256 := by
      unfold actionA
      rw [step99o231s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 2 * (codeMat 161 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 68 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 68) = codeMat 136 := by
      unfold actionA
      rw [step99o231s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 68 * (codeMat 161 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 1) = codeMat 64 := by
      unfold actionA
      rw [step99o231s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 160) = codeMat 34 := by
      unfold actionA
      rw [step99o231s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 160 * (codeMat 161 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 256) = codeMat 16 := by
      unfold actionA
      rw [step99o231s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 256 * (codeMat 161 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 16) = codeMat 4 := by
      unfold actionA
      rw [step99o231s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 16 * (codeMat 161 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step99o231s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 8 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact

theorem step99o231s1Dispatch :
    QuotientRankAtLeast (o231SourceU ⟨1, by omega⟩) 12 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 161) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 161) hP hQ orbit10W 12 orbit10_lb12
  have hMono : QuotientRankAtLeast step99o231ActualSource1 12 :=
    quotientRankAtLeast_mono step99o231s1_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o231s1_sourceU_le hMono

-- Source 2 (row 14): orbit 10, lb 12
def step99o231ActualSource2 : Submodule F2 Mat3 := spanCodes [256, 130, 68, 38, 16, 14, 1]

private theorem step99o231s2_sourceU_le :
    (o231SourceU ⟨2, by omega⟩) ≤ step99o231ActualSource2 := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 130, 68, 38, 16, 14, 1] (step99o231MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 132 + codeMat 34 + codeMat 12) ⊓ kerEvalFunc (codeMat 66 + codeMat 34 + codeMat 12)) at hM
    change (evalFunc (codeMat 132 + codeMat 34 + codeMat 12) M = 0 ∧ evalFunc (codeMat 66 + codeMat 34 + codeMat 12) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 130, 68, 38, 16, 14, 1] (step99o231MatrixCodeNat M) hbool
  rwa [step99o231_codeMat_matrixCode] at hspan

private theorem step99o231s2_QtInv :
    (codeMat 346 : Mat3).transpose⁻¹ = (codeMat 459 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 346 : Mat3).transpose * (codeMat 459 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o231s2_targetSpan_le_action :
    step99o231ActualSource2 ≤ actionW (codeMat 298) (codeMat 346) orbit10W := by
  apply step99o231_spanCodes_le_of_gens [256, 130, 68, 38, 16, 14, 1]
    (actionW (codeMat 298) (codeMat 346) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 298) (codeMat 346) (codeMat 256) = codeMat 256 := by
      unfold actionA
      rw [step99o231s2_QtInv]
      show (codeMat 298 : Mat3).transpose * codeMat 256 * (codeMat 459 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 24 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide)
    have hact : actionA (codeMat 298) (codeMat 346) (codeMat 24) = codeMat 130 := by
      unfold actionA
      rw [step99o231s2_QtInv]
      show (codeMat 298 : Mat3).transpose * codeMat 24 * (codeMat 459 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 298) (codeMat 346) (codeMat 160) = codeMat 68 := by
      unfold actionA
      rw [step99o231s2_QtInv]
      show (codeMat 298 : Mat3).transpose * codeMat 160 * (codeMat 459 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 508 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 508 (by decide)
    have hact : actionA (codeMat 298) (codeMat 346) (codeMat 508) = codeMat 38 := by
      unfold actionA
      rw [step99o231s2_QtInv]
      show (codeMat 298 : Mat3).transpose * codeMat 508 * (codeMat 459 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 3 (by decide)
    have hact : actionA (codeMat 298) (codeMat 346) (codeMat 3) = codeMat 16 := by
      unfold actionA
      rw [step99o231s2_QtInv]
      show (codeMat 298 : Mat3).transpose * codeMat 3 * (codeMat 459 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 510 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 510 (by decide)
    have hact : actionA (codeMat 298) (codeMat 346) (codeMat 510) = codeMat 14 := by
      unfold actionA
      rw [step99o231s2_QtInv]
      show (codeMat 298 : Mat3).transpose * codeMat 510 * (codeMat 459 : Mat3).transpose = codeMat 14
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 432 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 432 (by decide)
    have hact : actionA (codeMat 298) (codeMat 346) (codeMat 432) = codeMat 1 := by
      unfold actionA
      rw [step99o231s2_QtInv]
      show (codeMat 298 : Mat3).transpose * codeMat 432 * (codeMat 459 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact

theorem step99o231s2Dispatch :
    QuotientRankAtLeast (o231SourceU ⟨2, by omega⟩) 12 := by
  have hP : Invertible (codeMat 298 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 346 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 298) (codeMat 346) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 298) (codeMat 346) hP hQ orbit10W 12 orbit10_lb12
  have hMono : QuotientRankAtLeast step99o231ActualSource2 12 :=
    quotientRankAtLeast_mono step99o231s2_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o231s2_sourceU_le hMono

-- Source 3 (row 17): orbit 10, lb 12
def step99o231ActualSource3 : Submodule F2 Mat3 := spanCodes [256, 128, 66, 32, 16, 12, 1]

private theorem step99o231s3_sourceU_le :
    (o231SourceU ⟨3, by omega⟩) ≤ step99o231ActualSource3 := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 128, 66, 32, 16, 12, 1] (step99o231MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 66) ⊓ kerEvalFunc (codeMat 12)) at hM
    change (evalFunc (codeMat 66) M = 0 ∧ evalFunc (codeMat 12) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 128, 66, 32, 16, 12, 1] (step99o231MatrixCodeNat M) hbool
  rwa [step99o231_codeMat_matrixCode] at hspan

private theorem step99o231s3_QtInv :
    (codeMat 98 : Mat3).transpose⁻¹ = (codeMat 140 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 98 : Mat3).transpose * (codeMat 140 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o231s3_targetSpan_le_action :
    step99o231ActualSource3 ≤ actionW (codeMat 84) (codeMat 98) orbit10W := by
  apply step99o231_spanCodes_le_of_gens [256, 128, 66, 32, 16, 12, 1]
    (actionW (codeMat 84) (codeMat 98) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 98) (codeMat 2) = codeMat 256 := by
      unfold actionA
      rw [step99o231s3_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 140 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 98) (codeMat 1) = codeMat 128 := by
      unfold actionA
      rw [step99o231s3_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 140 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 84) (codeMat 98) (codeMat 68) = codeMat 66 := by
      unfold actionA
      rw [step99o231s3_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 68 * (codeMat 140 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 84) (codeMat 98) (codeMat 16) = codeMat 32 := by
      unfold actionA
      rw [step99o231s3_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 16 * (codeMat 140 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 98) (codeMat 8) = codeMat 16 := by
      unfold actionA
      rw [step99o231s3_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 140 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 84) (codeMat 98) (codeMat 160) = codeMat 12 := by
      unfold actionA
      rw [step99o231s3_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 160 * (codeMat 140 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 98) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step99o231s3_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 140 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact

theorem step99o231s3Dispatch :
    QuotientRankAtLeast (o231SourceU ⟨3, by omega⟩) 12 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 98) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 98) hP hQ orbit10W 12 orbit10_lb12
  have hMono : QuotientRankAtLeast step99o231ActualSource3 12 :=
    quotientRankAtLeast_mono step99o231s3_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o231s3_sourceU_le hMono

-- Source 4 (row 19): orbit 10, lb 12
def step99o231ActualSource4 : Submodule F2 Mat3 := spanCodes [256, 138, 72, 42, 16, 6, 1]

private theorem step99o231s4_sourceU_le :
    (o231SourceU ⟨4, by omega⟩) ≤ step99o231ActualSource4 := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 138, 72, 42, 16, 6, 1] (step99o231MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 132 + codeMat 34) ⊓ kerEvalFunc (codeMat 66 + codeMat 12)) at hM
    change (evalFunc (codeMat 132 + codeMat 34) M = 0 ∧ evalFunc (codeMat 66 + codeMat 12) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 138, 72, 42, 16, 6, 1] (step99o231MatrixCodeNat M) hbool
  rwa [step99o231_codeMat_matrixCode] at hspan

private theorem step99o231s4_QtInv :
    (codeMat 395 : Mat3).transpose⁻¹ = (codeMat 474 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 395 : Mat3).transpose * (codeMat 474 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o231s4_targetSpan_le_action :
    step99o231ActualSource4 ≤ actionW (codeMat 270) (codeMat 395) orbit10W := by
  apply step99o231_spanCodes_le_of_gens [256, 138, 72, 42, 16, 6, 1]
    (actionW (codeMat 270) (codeMat 395) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 270) (codeMat 395) (codeMat 256) = codeMat 256 := by
      unfold actionA
      rw [step99o231s4_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 256 * (codeMat 474 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 427 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 427 (by decide)
    have hact : actionA (codeMat 270) (codeMat 395) (codeMat 427) = codeMat 138 := by
      unfold actionA
      rw [step99o231s4_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 427 * (codeMat 474 : Mat3).transpose = codeMat 138
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 3 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 3 (by decide)
    have hact : actionA (codeMat 270) (codeMat 395) (codeMat 3) = codeMat 72 := by
      unfold actionA
      rw [step99o231s4_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 3 * (codeMat 474 : Mat3).transpose = codeMat 72
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 495 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 495 (by decide)
    have hact : actionA (codeMat 270) (codeMat 395) (codeMat 495) = codeMat 42 := by
      unfold actionA
      rw [step99o231s4_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 495 * (codeMat 474 : Mat3).transpose = codeMat 42
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 325 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 325 (by decide)
    have hact : actionA (codeMat 270) (codeMat 395) (codeMat 325) = codeMat 16 := by
      unfold actionA
      rw [step99o231s4_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 325 * (codeMat 474 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 270) (codeMat 395) (codeMat 8) = codeMat 6 := by
      unfold actionA
      rw [step99o231s4_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 8 * (codeMat 474 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 24 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide)
    have hact : actionA (codeMat 270) (codeMat 395) (codeMat 24) = codeMat 1 := by
      unfold actionA
      rw [step99o231s4_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 24 * (codeMat 474 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact

theorem step99o231s4Dispatch :
    QuotientRankAtLeast (o231SourceU ⟨4, by omega⟩) 12 := by
  have hP : Invertible (codeMat 270 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 395 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 270) (codeMat 395) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 270) (codeMat 395) hP hQ orbit10W 12 orbit10_lb12
  have hMono : QuotientRankAtLeast step99o231ActualSource4 12 :=
    quotientRankAtLeast_mono step99o231s4_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o231s4_sourceU_le hMono

-- Source 5 (row 21): orbit 10, lb 12
def step99o231ActualSource5 : Submodule F2 Mat3 := spanCodes [256, 134, 70, 36, 16, 10, 1]

private theorem step99o231s5_sourceU_le :
    (o231SourceU ⟨5, by omega⟩) ≤ step99o231ActualSource5 := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 134, 70, 36, 16, 10, 1] (step99o231MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 132 + codeMat 66 + codeMat 12) ⊓ kerEvalFunc (codeMat 34 + codeMat 12)) at hM
    change (evalFunc (codeMat 132 + codeMat 66 + codeMat 12) M = 0 ∧ evalFunc (codeMat 34 + codeMat 12) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 134, 70, 36, 16, 10, 1] (step99o231MatrixCodeNat M) hbool
  rwa [step99o231_codeMat_matrixCode] at hspan

private theorem step99o231s5_QtInv :
    (codeMat 236 : Mat3).transpose⁻¹ = (codeMat 123 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 236 : Mat3).transpose * (codeMat 123 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o231s5_targetSpan_le_action :
    step99o231ActualSource5 ≤ actionW (codeMat 156) (codeMat 236) orbit10W := by
  apply step99o231_spanCodes_le_of_gens [256, 134, 70, 36, 16, 10, 1]
    (actionW (codeMat 156) (codeMat 236) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 3 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 3 (by decide)
    have hact : actionA (codeMat 156) (codeMat 236) (codeMat 3) = codeMat 256 := by
      unfold actionA
      rw [step99o231s5_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 3 * (codeMat 123 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 508 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 508 (by decide)
    have hact : actionA (codeMat 156) (codeMat 236) (codeMat 508) = codeMat 134 := by
      unfold actionA
      rw [step99o231s5_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 508 * (codeMat 123 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 510 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 510 (by decide)
    have hact : actionA (codeMat 156) (codeMat 236) (codeMat 510) = codeMat 70 := by
      unfold actionA
      rw [step99o231s5_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 510 * (codeMat 123 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 24 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide)
    have hact : actionA (codeMat 156) (codeMat 236) (codeMat 24) = codeMat 36 := by
      unfold actionA
      rw [step99o231s5_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 24 * (codeMat 123 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 156) (codeMat 236) (codeMat 256) = codeMat 16 := by
      unfold actionA
      rw [step99o231s5_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 256 * (codeMat 123 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 156) (codeMat 236) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step99o231s5_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 160 * (codeMat 123 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 432 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 432 (by decide)
    have hact : actionA (codeMat 156) (codeMat 236) (codeMat 432) = codeMat 1 := by
      unfold actionA
      rw [step99o231s5_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 432 * (codeMat 123 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o231_codeMat_mem_actionW_of_witness hw hact

theorem step99o231s5Dispatch :
    QuotientRankAtLeast (o231SourceU ⟨5, by omega⟩) 12 := by
  have hP : Invertible (codeMat 156 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 236 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 156) (codeMat 236) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 156) (codeMat 236) hP hQ orbit10W 12 orbit10_lb12
  have hMono : QuotientRankAtLeast step99o231ActualSource5 12 :=
    quotientRankAtLeast_mono step99o231s5_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o231s5_sourceU_le hMono

theorem step99o231_all_dispatch (i : Fin 6) :
    QuotientRankAtLeast (o231SourceU i) (o231SourceLb i) := by
  fin_cases i
  · exact step99o231s0Dispatch
  · exact step99o231s1Dispatch
  · exact step99o231s2Dispatch
  · exact step99o231s3Dispatch
  · exact step99o231s4Dispatch
  · exact step99o231s5Dispatch

theorem step99_orbit231_lb15_unconditional :
    QuotientRankAtLeast o231W 15 :=
  o231Lb15 step99o231_all_dispatch

end QiushiMatmul
