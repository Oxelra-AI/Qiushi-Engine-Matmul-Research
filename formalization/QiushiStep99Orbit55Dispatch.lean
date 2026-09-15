import QiushiCodeSpanCore
import QiushiFlattenSeeds
import QiushiMonotonicity
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiOrbitTransport
import QiushiStep98Orbit55Consumer

set_option maxHeartbeats 800000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem step99o55_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step99o55MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step99o55_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step99o55MatrixCodeNat M) = M := by decide

lemma step99o55_codeMat_matrixCode (M : Mat3) :
    codeMat (step99o55MatrixCodeNat M) = M :=
  step99o55_codeMat_matrixCode_all M

private theorem step99o55_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step99o55_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

-- Source 0 (row 0): orbit 11, lb 12
def step99o55ActualSource0 : Submodule F2 Mat3 := spanCodes [256, 132, 32, 16, 12, 2, 1]

private theorem step99o55s0_sourceU_le :
    (o55SourceU ⟨0, by omega⟩) ≤ step99o55ActualSource0 := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 132, 32, 16, 12, 2, 1] (step99o55MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 140) ⊓ kerEvalFunc (codeMat 64)) at hM
    change (evalFunc (codeMat 140) M = 0 ∧ evalFunc (codeMat 64) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 132, 32, 16, 12, 2, 1] (step99o55MatrixCodeNat M) hbool
  rwa [step99o55_codeMat_matrixCode] at hspan

private theorem step99o55s0_QtInv :
    (codeMat 98 : Mat3).transpose⁻¹ = (codeMat 140 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 98 : Mat3).transpose * (codeMat 140 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o55s0_targetSpan_le_action :
    step99o55ActualSource0 ≤ actionW (codeMat 266) (codeMat 98) orbit11W := by
  apply step99o55_spanCodes_le_of_gens [256, 132, 32, 16, 12, 2, 1]
    (actionW (codeMat 266) (codeMat 98) orbit11W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 128 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 128 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 128) = codeMat 256 := by
      unfold actionA
      rw [step99o55s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 128 * (codeMat 140 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o55_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 80 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 80 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 80) = codeMat 132 := by
      unfold actionA
      rw [step99o55s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 80 * (codeMat 140 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o55_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 2) = codeMat 32 := by
      unfold actionA
      rw [step99o55s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 140 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o55_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step99o55s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 140 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o55_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 20 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 20 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 20) = codeMat 12 := by
      unfold actionA
      rw [step99o55s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 20 * (codeMat 140 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o55_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 8) = codeMat 2 := by
      unfold actionA
      rw [step99o55s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 140 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o55_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 32 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 32 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step99o55s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 140 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o55_codeMat_mem_actionW_of_witness hw hact

theorem step99o55s0Dispatch :
    QuotientRankAtLeast (o55SourceU ⟨0, by omega⟩) 12 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 98) orbit11W) 12 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 98) hP hQ orbit11W 12 orbit11_lb12
  have hMono : QuotientRankAtLeast step99o55ActualSource0 12 :=
    quotientRankAtLeast_mono step99o55s0_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o55s0_sourceU_le hMono

-- Source 1 (row 2): orbit 14, lb 12
def step99o55ActualSource1 : Submodule F2 Mat3 := spanCodes [272, 132, 68, 32, 12, 2, 1]

private theorem step99o55s1_sourceU_le :
    (o55SourceU ⟨1, by omega⟩) ≤ step99o55ActualSource1 := by
  intro M hM
  have hbool : spanContainsCodeCore [272, 132, 68, 32, 12, 2, 1] (step99o55MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 272) ⊓ kerEvalFunc (codeMat 140 + codeMat 64)) at hM
    change (evalFunc (codeMat 272) M = 0 ∧ evalFunc (codeMat 140 + codeMat 64) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 132, 68, 32, 12, 2, 1] (step99o55MatrixCodeNat M) hbool
  rwa [step99o55_codeMat_matrixCode] at hspan

private theorem step99o55s1_QtInv :
    (codeMat 318 : Mat3).transpose⁻¹ = (codeMat 299 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 318 : Mat3).transpose * (codeMat 299 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o55s1_targetSpan_le_action :
    step99o55ActualSource1 ≤ actionW (codeMat 481) (codeMat 318) orbit14W := by
  apply step99o55_spanCodes_le_of_gens [272, 132, 68, 32, 12, 2, 1]
    (actionW (codeMat 481) (codeMat 318) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 227 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 227 (by decide)
    have hact : actionA (codeMat 481) (codeMat 318) (codeMat 227) = codeMat 272 := by
      unfold actionA
      rw [step99o55s1_QtInv]
      show (codeMat 481 : Mat3).transpose * codeMat 227 * (codeMat 299 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o55_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 31 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 31 (by decide)
    have hact : actionA (codeMat 481) (codeMat 318) (codeMat 31) = codeMat 132 := by
      unfold actionA
      rw [step99o55s1_QtInv]
      show (codeMat 481 : Mat3).transpose * codeMat 31 * (codeMat 299 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o55_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 23 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 23 (by decide)
    have hact : actionA (codeMat 481) (codeMat 318) (codeMat 23) = codeMat 68 := by
      unfold actionA
      rw [step99o55s1_QtInv]
      show (codeMat 481 : Mat3).transpose * codeMat 23 * (codeMat 299 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o55_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 511 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 511 (by decide)
    have hact : actionA (codeMat 481) (codeMat 318) (codeMat 511) = codeMat 32 := by
      unfold actionA
      rw [step99o55s1_QtInv]
      show (codeMat 481 : Mat3).transpose * codeMat 511 * (codeMat 299 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o55_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 149 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 149 (by decide)
    have hact : actionA (codeMat 481) (codeMat 318) (codeMat 149) = codeMat 12 := by
      unfold actionA
      rw [step99o55s1_QtInv]
      show (codeMat 481 : Mat3).transpose * codeMat 149 * (codeMat 299 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o55_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 481) (codeMat 318) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [step99o55s1_QtInv]
      show (codeMat 481 : Mat3).transpose * codeMat 3 * (codeMat 299 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o55_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 481) (codeMat 318) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step99o55s1_QtInv]
      show (codeMat 481 : Mat3).transpose * codeMat 2 * (codeMat 299 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o55_codeMat_mem_actionW_of_witness hw hact

theorem step99o55s1Dispatch :
    QuotientRankAtLeast (o55SourceU ⟨1, by omega⟩) 12 := by
  have hP : Invertible (codeMat 481 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 318 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 481) (codeMat 318) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 481) (codeMat 318) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step99o55ActualSource1 12 :=
    quotientRankAtLeast_mono step99o55s1_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o55s1_sourceU_le hMono

-- Source 2 (row 3): orbit 14, lb 12
def step99o55ActualSource2 : Submodule F2 Mat3 := spanCodes [272, 132, 80, 32, 12, 2, 1]

private theorem step99o55s2_sourceU_le :
    (o55SourceU ⟨2, by omega⟩) ≤ step99o55ActualSource2 := by
  intro M hM
  have hbool : spanContainsCodeCore [272, 132, 80, 32, 12, 2, 1] (step99o55MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 272 + codeMat 64) ⊓ kerEvalFunc (codeMat 140)) at hM
    change (evalFunc (codeMat 272 + codeMat 64) M = 0 ∧ evalFunc (codeMat 140) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 12, 2, 1] (step99o55MatrixCodeNat M) hbool
  rwa [step99o55_codeMat_matrixCode] at hspan

private theorem step99o55s2_QtInv :
    (codeMat 492 : Mat3).transpose⁻¹ = (codeMat 115 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 492 : Mat3).transpose * (codeMat 115 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o55s2_targetSpan_le_action :
    step99o55ActualSource2 ≤ actionW (codeMat 103) (codeMat 492) orbit14W := by
  apply step99o55_spanCodes_le_of_gens [272, 132, 80, 32, 12, 2, 1]
    (actionW (codeMat 103) (codeMat 492) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 284 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 284 (by decide)
    have hact : actionA (codeMat 103) (codeMat 492) (codeMat 284) = codeMat 272 := by
      unfold actionA
      rw [step99o55s2_QtInv]
      show (codeMat 103 : Mat3).transpose * codeMat 284 * (codeMat 115 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o55_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 480 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 480 (by decide)
    have hact : actionA (codeMat 103) (codeMat 492) (codeMat 480) = codeMat 132 := by
      unfold actionA
      rw [step99o55s2_QtInv]
      show (codeMat 103 : Mat3).transpose * codeMat 480 * (codeMat 115 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o55_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 276 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 276 (by decide)
    have hact : actionA (codeMat 103) (codeMat 492) (codeMat 276) = codeMat 80 := by
      unfold actionA
      rw [step99o55s2_QtInv]
      show (codeMat 103 : Mat3).transpose * codeMat 276 * (codeMat 115 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o55_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 511 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 511 (by decide)
    have hact : actionA (codeMat 103) (codeMat 492) (codeMat 511) = codeMat 32 := by
      unfold actionA
      rw [step99o55s2_QtInv]
      show (codeMat 103 : Mat3).transpose * codeMat 511 * (codeMat 115 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o55_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 118 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 118 (by decide)
    have hact : actionA (codeMat 103) (codeMat 492) (codeMat 118) = codeMat 12 := by
      unfold actionA
      rw [step99o55s2_QtInv]
      show (codeMat 103 : Mat3).transpose * codeMat 118 * (codeMat 115 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o55_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 103) (codeMat 492) (codeMat 256) = codeMat 2 := by
      unfold actionA
      rw [step99o55s2_QtInv]
      show (codeMat 103 : Mat3).transpose * codeMat 256 * (codeMat 115 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o55_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 103) (codeMat 492) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step99o55s2_QtInv]
      show (codeMat 103 : Mat3).transpose * codeMat 384 * (codeMat 115 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o55_codeMat_mem_actionW_of_witness hw hact

theorem step99o55s2Dispatch :
    QuotientRankAtLeast (o55SourceU ⟨2, by omega⟩) 12 := by
  have hP : Invertible (codeMat 103 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 492 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 103) (codeMat 492) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 103) (codeMat 492) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step99o55ActualSource2 12 :=
    quotientRankAtLeast_mono step99o55s2_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o55s2_sourceU_le hMono

-- Source 3 (row 5): orbit 7, lb 9
def step99o55ActualSource3 : Submodule F2 Mat3 := spanCodes [272, 128, 32, 8, 4, 2, 1]

private theorem step99o55s3_sourceU_le :
    (o55SourceU ⟨3, by omega⟩) ≤ step99o55ActualSource3 := by
  intro M hM
  have hbool : spanContainsCodeCore [272, 128, 32, 8, 4, 2, 1] (step99o55MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 272) ⊓ kerEvalFunc (codeMat 64)) at hM
    change (evalFunc (codeMat 272) M = 0 ∧ evalFunc (codeMat 64) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 4, 2, 1] (step99o55MatrixCodeNat M) hbool
  rwa [step99o55_codeMat_matrixCode] at hspan

private theorem step99o55s3_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o55s3_targetSpan_le_action :
    step99o55ActualSource3 ≤ actionW (codeMat 273) (codeMat 140) flatW_7 := by
  apply step99o55_spanCodes_le_of_gens [272, 128, 32, 8, 4, 2, 1]
    (actionW (codeMat 273) (codeMat 140) flatW_7)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 96 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 96 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 96) = codeMat 272 := by
      unfold actionA
      rw [step99o55s3_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 96 * (codeMat 98 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o55_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 256 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 256) = codeMat 128 := by
      unfold actionA
      rw [step99o55s3_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 256 * (codeMat 98 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o55_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step99o55s3_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o55_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 16 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 16 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 16) = codeMat 8 := by
      unfold actionA
      rw [step99o55s3_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 16 * (codeMat 98 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o55_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 1) = codeMat 4 := by
      unfold actionA
      rw [step99o55s3_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o55_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 4 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 4 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 4) = codeMat 2 := by
      unfold actionA
      rw [step99o55s3_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 4 * (codeMat 98 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o55_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step99o55s3_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o55_codeMat_mem_actionW_of_witness hw hact

theorem step99o55s3Dispatch :
    QuotientRankAtLeast (o55SourceU ⟨3, by omega⟩) 9 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 140) flatW_7) 9 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 140) hP hQ flatW_7 9 flatSeed_7
  have hMono : QuotientRankAtLeast step99o55ActualSource3 9 :=
    quotientRankAtLeast_mono step99o55s3_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o55s3_sourceU_le hMono

-- Source 4 (row 8): orbit 3, lb 9
def step99o55ActualSource4 : Submodule F2 Mat3 := spanCodes [260, 132, 64, 32, 20, 12, 2, 1]

private theorem step99o55s4_sourceU_le :
    (o55SourceU ⟨4, by omega⟩) ≤ step99o55ActualSource4 := by
  intro M hM
  have hbool : spanContainsCodeCore [260, 132, 64, 32, 20, 12, 2, 1] (step99o55MatrixCodeNat M) = true := by
    change M ∈ kerEvalFunc (codeMat 272 + codeMat 140) at hM
    change evalFunc (codeMat 272 + codeMat 140) M = 0 at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 132, 64, 32, 20, 12, 2, 1] (step99o55MatrixCodeNat M) hbool
  rwa [step99o55_codeMat_matrixCode] at hspan

private theorem step99o55s4_QtInv :
    (codeMat 412 : Mat3).transpose⁻¹ = (codeMat 111 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 412 : Mat3).transpose * (codeMat 111 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o55s4_targetSpan_le_action :
    step99o55ActualSource4 ≤ actionW (codeMat 84) (codeMat 412) flatW_3 := by
  apply step99o55_spanCodes_le_of_gens [260, 132, 64, 32, 20, 12, 2, 1]
    (actionW (codeMat 84) (codeMat 412) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 325 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 325 (by decide)
    have hact : actionA (codeMat 84) (codeMat 412) (codeMat 325) = codeMat 260 := by
      unfold actionA
      rw [step99o55s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 325 * (codeMat 111 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o55_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 326 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 326 (by decide)
    have hact : actionA (codeMat 84) (codeMat 412) (codeMat 326) = codeMat 132 := by
      unfold actionA
      rw [step99o55s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 326 * (codeMat 111 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o55_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 412) (codeMat 2) = codeMat 64 := by
      unfold actionA
      rw [step99o55s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 111 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o55_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 40 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 84) (codeMat 412) (codeMat 40) = codeMat 32 := by
      unfold actionA
      rw [step99o55s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 40 * (codeMat 111 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o55_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 368 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 368 (by decide)
    have hact : actionA (codeMat 84) (codeMat 412) (codeMat 368) = codeMat 20 := by
      unfold actionA
      rw [step99o55s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 368 * (codeMat 111 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o55_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 336 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 336 (by decide)
    have hact : actionA (codeMat 84) (codeMat 412) (codeMat 336) = codeMat 12 := by
      unfold actionA
      rw [step99o55s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 336 * (codeMat 111 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o55_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 412) (codeMat 384) = codeMat 2 := by
      unfold actionA
      rw [step99o55s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 111 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o55_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 128 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 412) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step99o55s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 111 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o55_codeMat_mem_actionW_of_witness hw hact

theorem step99o55s4Dispatch :
    QuotientRankAtLeast (o55SourceU ⟨4, by omega⟩) 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 412 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 412) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 412) hP hQ flatW_3 9 flatSeed_3
  have hMono : QuotientRankAtLeast step99o55ActualSource4 9 :=
    quotientRankAtLeast_mono step99o55s4_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o55s4_sourceU_le hMono

theorem step99o55_all_dispatch (i : Fin 5) :
    QuotientRankAtLeast (o55SourceU i) (o55SourceLb i) := by
  fin_cases i
  · exact step99o55s0Dispatch
  · exact step99o55s1Dispatch
  · exact step99o55s2Dispatch
  · exact step99o55s3Dispatch
  · exact step99o55s4Dispatch

theorem step99_orbit55_lb14_unconditional :
    QuotientRankAtLeast o55W 14 :=
  o55Lb14 step99o55_all_dispatch

end QiushiMatmul
