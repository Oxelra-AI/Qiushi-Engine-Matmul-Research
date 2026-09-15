import QiushiCodeSpanCore
import QiushiFlattenSeeds
import QiushiMonotonicity
import QiushiOrbit14FP
import QiushiOrbitTransport
import QiushiStep81Qdim2Generated
import QiushiStep98Orbit77Consumer
import QiushiTransposeTransport

set_option maxHeartbeats 800000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem step99o77_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step99o77MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step99o77_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step99o77MatrixCodeNat M) = M := by decide

lemma step99o77_codeMat_matrixCode (M : Mat3) :
    codeMat (step99o77MatrixCodeNat M) = M :=
  step99o77_codeMat_matrixCode_all M

private theorem step99o77_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step99o77_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

private theorem step99o77_codeMat_mem_transposeW_of_witness
    {V : Submodule F2 Mat3} {pre tpre : Nat}
    (h_mem : codeMat tpre ∈ V)
    (h_trans : (codeMat tpre : Mat3).transpose = codeMat pre) :
    codeMat pre ∈ transposeW V := by
  change ∃ X, X ∈ V ∧ transposeLinearMap X = codeMat pre
  exact ⟨codeMat tpre, h_mem, h_trans⟩

-- Source 0 (row 0): orbit 17, lb 14
def step99o77ActualSource0 : Submodule F2 Mat3 := spanCodes [260, 128, 70, 38, 20, 10, 1]

private theorem step99o77s0_sourceU_le :
    (o77SourceU ⟨0, by omega⟩) ≤ step99o77ActualSource0 := by
  intro M hM
  have hbool : spanContainsCodeCore [260, 128, 70, 38, 20, 10, 1] (step99o77MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 276 + codeMat 10) ⊓ kerEvalFunc (codeMat 96 + codeMat 10)) at hM
    change (evalFunc (codeMat 276 + codeMat 10) M = 0 ∧ evalFunc (codeMat 96 + codeMat 10) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 128, 70, 38, 20, 10, 1] (step99o77MatrixCodeNat M) hbool
  rwa [step99o77_codeMat_matrixCode] at hspan

private theorem step99o77s0_QtInv :
    (codeMat 103 : Mat3).transpose⁻¹ = (codeMat 188 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 103 : Mat3).transpose * (codeMat 188 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o77s0_targetSpan_le_action :
    step99o77ActualSource0 ≤ actionW (codeMat 500) (codeMat 103) step81o17s4Wspan := by
  apply step99o77_spanCodes_le_of_gens [260, 128, 70, 38, 20, 10, 1]
    (actionW (codeMat 500) (codeMat 103) step81o17s4Wspan)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 219 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 219 (by decide)
    have hact : actionA (codeMat 500) (codeMat 103) (codeMat 219) = codeMat 260 := by
      unfold actionA
      rw [step99o77s0_QtInv]
      show (codeMat 500 : Mat3).transpose * codeMat 219 * (codeMat 188 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o77_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 500) (codeMat 103) (codeMat 1) = codeMat 128 := by
      unfold actionA
      rw [step99o77s0_QtInv]
      show (codeMat 500 : Mat3).transpose * codeMat 1 * (codeMat 188 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o77_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 149 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 149 (by decide)
    have hact : actionA (codeMat 500) (codeMat 103) (codeMat 149) = codeMat 70 := by
      unfold actionA
      rw [step99o77s0_QtInv]
      show (codeMat 500 : Mat3).transpose * codeMat 149 * (codeMat 188 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o77_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 139 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 139 (by decide)
    have hact : actionA (codeMat 500) (codeMat 103) (codeMat 139) = codeMat 38 := by
      unfold actionA
      rw [step99o77s0_QtInv]
      show (codeMat 500 : Mat3).transpose * codeMat 139 * (codeMat 188 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o77_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 209 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 209 (by decide)
    have hact : actionA (codeMat 500) (codeMat 103) (codeMat 209) = codeMat 20 := by
      unfold actionA
      rw [step99o77s0_QtInv]
      show (codeMat 500 : Mat3).transpose * codeMat 209 * (codeMat 188 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o77_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 101 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 101 (by decide)
    have hact : actionA (codeMat 500) (codeMat 103) (codeMat 101) = codeMat 10 := by
      unfold actionA
      rw [step99o77s0_QtInv]
      show (codeMat 500 : Mat3).transpose * codeMat 101 * (codeMat 188 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o77_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 360 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 360 (by decide)
    have hact : actionA (codeMat 500) (codeMat 103) (codeMat 360) = codeMat 1 := by
      unfold actionA
      rw [step99o77s0_QtInv]
      show (codeMat 500 : Mat3).transpose * codeMat 360 * (codeMat 188 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o77_codeMat_mem_actionW_of_witness hw hact

theorem step99o77s0Dispatch :
    QuotientRankAtLeast (o77SourceU ⟨0, by omega⟩) 14 := by
  have hP : Invertible (codeMat 500 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 103 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 500) (codeMat 103) step81o17s4Wspan) 14 :=
    @quotientRankAtLeast_action (codeMat 500) (codeMat 103) hP hQ step81o17s4Wspan 14 step81o17s4Span_lb
  have hMono : QuotientRankAtLeast step99o77ActualSource0 14 :=
    quotientRankAtLeast_mono step99o77s0_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o77s0_sourceU_le hMono

-- Source 1 (row 1): orbit 14, lb 12
def step99o77ActualSource1 : Submodule F2 Mat3 := spanCodes [260, 128, 96, 20, 8, 2, 1]

private theorem step99o77s1_sourceU_le :
    (o77SourceU ⟨1, by omega⟩) ≤ step99o77ActualSource1 := by
  intro M hM
  have hbool : spanContainsCodeCore [260, 128, 96, 20, 8, 2, 1] (step99o77MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 276) ⊓ kerEvalFunc (codeMat 96)) at hM
    change (evalFunc (codeMat 276) M = 0 ∧ evalFunc (codeMat 96) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 8, 2, 1] (step99o77MatrixCodeNat M) hbool
  rwa [step99o77_codeMat_matrixCode] at hspan

private theorem step99o77s1_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o77s1_targetSpan_le_action :
    step99o77ActualSource1 ≤ actionW (codeMat 337) (codeMat 273) orbit14W := by
  apply step99o77_spanCodes_le_of_gens [260, 128, 96, 20, 8, 2, 1]
    (actionW (codeMat 337) (codeMat 273) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 337) (codeMat 273) (codeMat 256) = codeMat 260 := by
      unfold actionA
      rw [step99o77s1_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 256 * (codeMat 273 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o77_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 130 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 130 (by decide)
    have hact : actionA (codeMat 337) (codeMat 273) (codeMat 130) = codeMat 128 := by
      unfold actionA
      rw [step99o77s1_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 130 * (codeMat 273 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o77_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 97 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 97 (by decide)
    have hact : actionA (codeMat 337) (codeMat 273) (codeMat 97) = codeMat 96 := by
      unfold actionA
      rw [step99o77s1_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 97 * (codeMat 273 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o77_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 20 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 20 (by decide)
    have hact : actionA (codeMat 337) (codeMat 273) (codeMat 20) = codeMat 20 := by
      unfold actionA
      rw [step99o77s1_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 20 * (codeMat 273 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o77_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 337) (codeMat 273) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step99o77s1_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 8 * (codeMat 273 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o77_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 337) (codeMat 273) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step99o77s1_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o77_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 337) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step99o77s1_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o77_codeMat_mem_actionW_of_witness hw hact

theorem step99o77s1Dispatch :
    QuotientRankAtLeast (o77SourceU ⟨1, by omega⟩) 12 := by
  have hP : Invertible (codeMat 337 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 337) (codeMat 273) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 337) (codeMat 273) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step99o77ActualSource1 12 :=
    quotientRankAtLeast_mono step99o77s1_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o77s1_sourceU_le hMono

-- Source 2 (row 2): orbit 14, lb 12
def step99o77ActualSource2 : Submodule F2 Mat3 := spanCodes [256, 128, 96, 16, 10, 4, 1]

private theorem step99o77s2_sourceU_le :
    (o77SourceU ⟨2, by omega⟩) ≤ step99o77ActualSource2 := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 128, 96, 16, 10, 4, 1] (step99o77MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 96) ⊓ kerEvalFunc (codeMat 10)) at hM
    change (evalFunc (codeMat 96) M = 0 ∧ evalFunc (codeMat 10) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 128, 96, 16, 10, 4, 1] (step99o77MatrixCodeNat M) hbool
  rwa [step99o77_codeMat_matrixCode] at hspan

private theorem step99o77s2_QtInv :
    (codeMat 98 : Mat3).transpose⁻¹ = (codeMat 140 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 98 : Mat3).transpose * (codeMat 140 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o77s2_targetSpan_le_action :
    step99o77ActualSource2 ≤ actionW (codeMat 84) (codeMat 98) orbit14W := by
  apply step99o77_spanCodes_le_of_gens [256, 128, 96, 16, 10, 4, 1]
    (actionW (codeMat 84) (codeMat 98) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 98) (codeMat 2) = codeMat 256 := by
      unfold actionA
      rw [step99o77s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 140 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o77_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 98) (codeMat 1) = codeMat 128 := by
      unfold actionA
      rw [step99o77s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 140 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o77_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 20 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 20 (by decide)
    have hact : actionA (codeMat 84) (codeMat 98) (codeMat 20) = codeMat 96 := by
      unfold actionA
      rw [step99o77s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 20 * (codeMat 140 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o77_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 98) (codeMat 8) = codeMat 16 := by
      unfold actionA
      rw [step99o77s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 140 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o77_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 84) (codeMat 98) (codeMat 96) = codeMat 10 := by
      unfold actionA
      rw [step99o77s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 96 * (codeMat 140 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o77_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 98) (codeMat 128) = codeMat 4 := by
      unfold actionA
      rw [step99o77s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 140 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o77_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 98) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step99o77s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 140 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o77_codeMat_mem_actionW_of_witness hw hact

theorem step99o77s2Dispatch :
    QuotientRankAtLeast (o77SourceU ⟨2, by omega⟩) 12 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 98) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 98) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step99o77ActualSource2 12 :=
    quotientRankAtLeast_mono step99o77s2_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o77s2_sourceU_le hMono

-- Source 3 (row 4): orbit 14, lb 12
def step99o77ActualSource3 : Submodule F2 Mat3 := spanCodes [260, 128, 64, 32, 20, 10, 1]

private theorem step99o77s3_sourceU_le :
    (o77SourceU ⟨3, by omega⟩) ≤ step99o77ActualSource3 := by
  intro M hM
  have hbool : spanContainsCodeCore [260, 128, 64, 32, 20, 10, 1] (step99o77MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 276) ⊓ kerEvalFunc (codeMat 10)) at hM
    change (evalFunc (codeMat 276) M = 0 ∧ evalFunc (codeMat 10) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 128, 64, 32, 20, 10, 1] (step99o77MatrixCodeNat M) hbool
  rwa [step99o77_codeMat_matrixCode] at hspan

private theorem step99o77s3_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o77s3_targetSpan_le_action :
    step99o77ActualSource3 ≤ actionW (codeMat 277) (codeMat 140) orbit14W := by
  apply step99o77_spanCodes_le_of_gens [260, 128, 64, 32, 20, 10, 1]
    (actionW (codeMat 277) (codeMat 140) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 277) (codeMat 140) (codeMat 1) = codeMat 260 := by
      unfold actionA
      rw [step99o77s3_QtInv]
      show (codeMat 277 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o77_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 277) (codeMat 140) (codeMat 256) = codeMat 128 := by
      unfold actionA
      rw [step99o77s3_QtInv]
      show (codeMat 277 : Mat3).transpose * codeMat 256 * (codeMat 98 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o77_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 277) (codeMat 140) (codeMat 128) = codeMat 64 := by
      unfold actionA
      rw [step99o77s3_QtInv]
      show (codeMat 277 : Mat3).transpose * codeMat 128 * (codeMat 98 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o77_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 277) (codeMat 140) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step99o77s3_QtInv]
      show (codeMat 277 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o77_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 97 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 97 (by decide)
    have hact : actionA (codeMat 277) (codeMat 140) (codeMat 97) = codeMat 20 := by
      unfold actionA
      rw [step99o77s3_QtInv]
      show (codeMat 277 : Mat3).transpose * codeMat 97 * (codeMat 98 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o77_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 276 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 276 (by decide)
    have hact : actionA (codeMat 277) (codeMat 140) (codeMat 276) = codeMat 10 := by
      unfold actionA
      rw [step99o77s3_QtInv]
      show (codeMat 277 : Mat3).transpose * codeMat 276 * (codeMat 98 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o77_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 130 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 130 (by decide)
    have hact : actionA (codeMat 277) (codeMat 140) (codeMat 130) = codeMat 1 := by
      unfold actionA
      rw [step99o77s3_QtInv]
      show (codeMat 277 : Mat3).transpose * codeMat 130 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o77_codeMat_mem_actionW_of_witness hw hact

theorem step99o77s3Dispatch :
    QuotientRankAtLeast (o77SourceU ⟨3, by omega⟩) 12 := by
  have hP : Invertible (codeMat 277 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 277) (codeMat 140) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 277) (codeMat 140) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step99o77ActualSource3 12 :=
    quotientRankAtLeast_mono step99o77s3_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o77s3_sourceU_le hMono

-- Source 4 (row 7): orbit 3, lb 9
def step99o77ActualSource4 : Submodule F2 Mat3 := spanCodes [258, 128, 66, 34, 18, 10, 6, 1]

private theorem step99o77s4_sourceU_le :
    (o77SourceU ⟨4, by omega⟩) ≤ step99o77ActualSource4 := by
  intro M hM
  have hbool : spanContainsCodeCore [258, 128, 66, 34, 18, 10, 6, 1] (step99o77MatrixCodeNat M) = true := by
    change M ∈ kerEvalFunc (codeMat 276 + codeMat 96 + codeMat 10) at hM
    change evalFunc (codeMat 276 + codeMat 96 + codeMat 10) M = 0 at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 128, 66, 34, 18, 10, 6, 1] (step99o77MatrixCodeNat M) hbool
  rwa [step99o77_codeMat_matrixCode] at hspan

private theorem step99o77s4_QtInv :
    (codeMat 382 : Mat3).transpose⁻¹ = (codeMat 499 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 382 : Mat3).transpose * (codeMat 499 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o77s4_targetSpan_le_action :
    step99o77ActualSource4 ≤ actionW (codeMat 84) (codeMat 382) flatW_3 := by
  apply step99o77_spanCodes_le_of_gens [258, 128, 66, 34, 18, 10, 6, 1]
    (actionW (codeMat 84) (codeMat 382) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 199 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 199 (by decide)
    have hact : actionA (codeMat 84) (codeMat 382) (codeMat 199) = codeMat 258 := by
      unfold actionA
      rw [step99o77s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 199 * (codeMat 499 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o77_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 3 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 84) (codeMat 382) (codeMat 3) = codeMat 128 := by
      unfold actionA
      rw [step99o77s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 3 * (codeMat 499 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o77_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 198 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 198 (by decide)
    have hact : actionA (codeMat 84) (codeMat 382) (codeMat 198) = codeMat 66 := by
      unfold actionA
      rw [step99o77s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 198 * (codeMat 499 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o77_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 248 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 248 (by decide)
    have hact : actionA (codeMat 84) (codeMat 382) (codeMat 248) = codeMat 34 := by
      unfold actionA
      rw [step99o77s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 248 * (codeMat 499 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o77_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 216 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 216 (by decide)
    have hact : actionA (codeMat 84) (codeMat 382) (codeMat 216) = codeMat 18 := by
      unfold actionA
      rw [step99o77s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 216 * (codeMat 499 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o77_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 240 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 240 (by decide)
    have hact : actionA (codeMat 84) (codeMat 382) (codeMat 240) = codeMat 10 := by
      unfold actionA
      rw [step99o77s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 240 * (codeMat 499 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o77_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 382) (codeMat 256) = codeMat 6 := by
      unfold actionA
      rw [step99o77s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 499 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o77_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 382) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step99o77s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 499 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o77_codeMat_mem_actionW_of_witness hw hact

theorem step99o77s4Dispatch :
    QuotientRankAtLeast (o77SourceU ⟨4, by omega⟩) 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 382 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 382) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 382) hP hQ flatW_3 9 flatSeed_3
  have hMono : QuotientRankAtLeast step99o77ActualSource4 9 :=
    quotientRankAtLeast_mono step99o77s4_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o77s4_sourceU_le hMono

theorem step99o77_all_dispatch (i : Fin 5) :
    QuotientRankAtLeast (o77SourceU i) (o77SourceLb i) := by
  fin_cases i
  · exact step99o77s0Dispatch
  · exact step99o77s1Dispatch
  · exact step99o77s2Dispatch
  · exact step99o77s3Dispatch
  · exact step99o77s4Dispatch

theorem step99_orbit77_lb15_unconditional :
    QuotientRankAtLeast o77W 15 :=
  o77Lb15 step99o77_all_dispatch

end QiushiMatmul
