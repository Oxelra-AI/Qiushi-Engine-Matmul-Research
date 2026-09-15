import QiushiCodeSpanCore
import QiushiFlattenSeeds
import QiushiMonotonicity
import QiushiOrbit11FP
import QiushiOrbitTransport
import QiushiStep98Orbit34Consumer

set_option maxHeartbeats 800000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem step99o34_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step99o34MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step99o34_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step99o34MatrixCodeNat M) = M := by decide

lemma step99o34_codeMat_matrixCode (M : Mat3) :
    codeMat (step99o34MatrixCodeNat M) = M :=
  step99o34_codeMat_matrixCode_all M

private theorem step99o34_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step99o34_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

-- Source 0 (row 0): orbit 11, lb 12
def step99o34ActualSource0 : Submodule F2 Mat3 := spanCodes [256, 68, 32, 20, 8, 2, 1]

private theorem step99o34s0_sourceU_le :
    (o34SourceU ⟨0, by omega⟩) ≤ step99o34ActualSource0 := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 68, 32, 20, 8, 2, 1] (step99o34MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 128) ⊓ kerEvalFunc (codeMat 84)) at hM
    change (evalFunc (codeMat 128) M = 0 ∧ evalFunc (codeMat 84) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 68, 32, 20, 8, 2, 1] (step99o34MatrixCodeNat M) hbool
  rwa [step99o34_codeMat_matrixCode] at hspan

private theorem step99o34s0_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o34s0_targetSpan_le_action :
    step99o34ActualSource0 ≤ actionW (codeMat 266) (codeMat 161) orbit11W := by
  apply step99o34_spanCodes_le_of_gens [256, 68, 32, 20, 8, 2, 1]
    (actionW (codeMat 266) (codeMat 161) orbit11W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 128 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 128 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 128) = codeMat 256 := by
      unfold actionA
      rw [step99o34s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 128 * (codeMat 161 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o34_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 80 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 80 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 80) = codeMat 68 := by
      unfold actionA
      rw [step99o34s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 80 * (codeMat 161 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o34_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 2) = codeMat 32 := by
      unfold actionA
      rw [step99o34s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 161 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o34_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 20 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 20 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 20) = codeMat 20 := by
      unfold actionA
      rw [step99o34s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 20 * (codeMat 161 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o34_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 1) = codeMat 8 := by
      unfold actionA
      rw [step99o34s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o34_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 32 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 32) = codeMat 2 := by
      unfold actionA
      rw [step99o34s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 161 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o34_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step99o34s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o34_codeMat_mem_actionW_of_witness hw hact

theorem step99o34s0Dispatch :
    QuotientRankAtLeast (o34SourceU ⟨0, by omega⟩) 12 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 161) orbit11W) 12 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 161) hP hQ orbit11W 12 orbit11_lb12
  have hMono : QuotientRankAtLeast step99o34ActualSource0 12 :=
    quotientRankAtLeast_mono step99o34s0_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o34s0_sourceU_le hMono

-- Source 1 (row 1): orbit 11, lb 12
def step99o34ActualSource1 : Submodule F2 Mat3 := spanCodes [256, 68, 36, 20, 8, 2, 1]

private theorem step99o34s1_sourceU_le :
    (o34SourceU ⟨1, by omega⟩) ≤ step99o34ActualSource1 := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 68, 36, 20, 8, 2, 1] (step99o34MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 128) ⊓ kerEvalFunc (codeMat 84 + codeMat 32)) at hM
    change (evalFunc (codeMat 128) M = 0 ∧ evalFunc (codeMat 84 + codeMat 32) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 68, 36, 20, 8, 2, 1] (step99o34MatrixCodeNat M) hbool
  rwa [step99o34_codeMat_matrixCode] at hspan

private theorem step99o34s1_QtInv :
    (codeMat 177 : Mat3).transpose⁻¹ = (codeMat 417 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 177 : Mat3).transpose * (codeMat 417 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o34s1_targetSpan_le_action :
    step99o34ActualSource1 ≤ actionW (codeMat 275) (codeMat 177) orbit11W := by
  apply step99o34_spanCodes_le_of_gens [256, 68, 36, 20, 8, 2, 1]
    (actionW (codeMat 275) (codeMat 177) orbit11W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 128 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 128 (by decide)
    have hact : actionA (codeMat 275) (codeMat 177) (codeMat 128) = codeMat 256 := by
      unfold actionA
      rw [step99o34s1_QtInv]
      show (codeMat 275 : Mat3).transpose * codeMat 128 * (codeMat 417 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o34_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 82 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 82 (by decide)
    have hact : actionA (codeMat 275) (codeMat 177) (codeMat 82) = codeMat 68 := by
      unfold actionA
      rw [step99o34s1_QtInv]
      show (codeMat 275 : Mat3).transpose * codeMat 82 * (codeMat 417 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o34_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 2 (by decide)
    have hact : actionA (codeMat 275) (codeMat 177) (codeMat 2) = codeMat 36 := by
      unfold actionA
      rw [step99o34s1_QtInv]
      show (codeMat 275 : Mat3).transpose * codeMat 2 * (codeMat 417 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o34_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 34 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 34 (by decide)
    have hact : actionA (codeMat 275) (codeMat 177) (codeMat 34) = codeMat 20 := by
      unfold actionA
      rw [step99o34s1_QtInv]
      show (codeMat 275 : Mat3).transpose * codeMat 34 * (codeMat 417 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o34_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 8 (by decide)
    have hact : actionA (codeMat 275) (codeMat 177) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step99o34s1_QtInv]
      show (codeMat 275 : Mat3).transpose * codeMat 8 * (codeMat 417 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o34_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 54 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 54 (by decide)
    have hact : actionA (codeMat 275) (codeMat 177) (codeMat 54) = codeMat 2 := by
      unfold actionA
      rw [step99o34s1_QtInv]
      show (codeMat 275 : Mat3).transpose * codeMat 54 * (codeMat 417 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o34_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 9 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 9 (by decide)
    have hact : actionA (codeMat 275) (codeMat 177) (codeMat 9) = codeMat 1 := by
      unfold actionA
      rw [step99o34s1_QtInv]
      show (codeMat 275 : Mat3).transpose * codeMat 9 * (codeMat 417 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o34_codeMat_mem_actionW_of_witness hw hact

theorem step99o34s1Dispatch :
    QuotientRankAtLeast (o34SourceU ⟨1, by omega⟩) 12 := by
  have hP : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 275) (codeMat 177) orbit11W) 12 :=
    @quotientRankAtLeast_action (codeMat 275) (codeMat 177) hP hQ orbit11W 12 orbit11_lb12
  have hMono : QuotientRankAtLeast step99o34ActualSource1 12 :=
    quotientRankAtLeast_mono step99o34s1_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o34s1_sourceU_le hMono

-- Source 2 (row 2): orbit 11, lb 12
def step99o34ActualSource2 : Submodule F2 Mat3 := spanCodes [256, 128, 68, 20, 8, 2, 1]

private theorem step99o34s2_sourceU_le :
    (o34SourceU ⟨2, by omega⟩) ≤ step99o34ActualSource2 := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 128, 68, 20, 8, 2, 1] (step99o34MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 84) ⊓ kerEvalFunc (codeMat 32)) at hM
    change (evalFunc (codeMat 84) M = 0 ∧ evalFunc (codeMat 32) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 20, 8, 2, 1] (step99o34MatrixCodeNat M) hbool
  rwa [step99o34_codeMat_matrixCode] at hspan

private theorem step99o34s2_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o34s2_targetSpan_le_action :
    step99o34ActualSource2 ≤ actionW (codeMat 161) (codeMat 266) orbit11W := by
  apply step99o34_spanCodes_le_of_gens [256, 128, 68, 20, 8, 2, 1]
    (actionW (codeMat 161) (codeMat 266) orbit11W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 32 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 32 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 32) = codeMat 256 := by
      unfold actionA
      rw [step99o34s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 32 * (codeMat 266 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o34_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 8 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 8 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 8) = codeMat 128 := by
      unfold actionA
      rw [step99o34s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 8 * (codeMat 266 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o34_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 20 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 20 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 20) = codeMat 68 := by
      unfold actionA
      rw [step99o34s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 20 * (codeMat 266 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o34_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 68 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 68 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 68) = codeMat 20 := by
      unfold actionA
      rw [step99o34s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 68 * (codeMat 266 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o34_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 128 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 128 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 128) = codeMat 8 := by
      unfold actionA
      rw [step99o34s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 128 * (codeMat 266 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o34_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 1) = codeMat 2 := by
      unfold actionA
      rw [step99o34s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o34_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step99o34s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o34_codeMat_mem_actionW_of_witness hw hact

theorem step99o34s2Dispatch :
    QuotientRankAtLeast (o34SourceU ⟨2, by omega⟩) 12 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 266) orbit11W) 12 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 266) hP hQ orbit11W 12 orbit11_lb12
  have hMono : QuotientRankAtLeast step99o34ActualSource2 12 :=
    quotientRankAtLeast_mono step99o34s2_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o34s2_sourceU_le hMono

-- Source 3 (row 3): orbit 11, lb 12
def step99o34ActualSource3 : Submodule F2 Mat3 := spanCodes [256, 132, 68, 20, 8, 2, 1]

private theorem step99o34s3_sourceU_le :
    (o34SourceU ⟨3, by omega⟩) ≤ step99o34ActualSource3 := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 132, 68, 20, 8, 2, 1] (step99o34MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 128 + codeMat 84) ⊓ kerEvalFunc (codeMat 32)) at hM
    change (evalFunc (codeMat 128 + codeMat 84) M = 0 ∧ evalFunc (codeMat 32) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 132, 68, 20, 8, 2, 1] (step99o34MatrixCodeNat M) hbool
  rwa [step99o34_codeMat_matrixCode] at hspan

private theorem step99o34s3_QtInv :
    (codeMat 282 : Mat3).transpose⁻¹ = (codeMat 267 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 282 : Mat3).transpose * (codeMat 267 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o34s3_targetSpan_le_action :
    step99o34ActualSource3 ≤ actionW (codeMat 161) (codeMat 282) orbit11W := by
  apply step99o34_spanCodes_le_of_gens [256, 132, 68, 20, 8, 2, 1]
    (actionW (codeMat 161) (codeMat 282) orbit11W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 32 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 32 (by decide)
    have hact : actionA (codeMat 161) (codeMat 282) (codeMat 32) = codeMat 256 := by
      unfold actionA
      rw [step99o34s3_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 32 * (codeMat 267 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o34_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 28 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 28 (by decide)
    have hact : actionA (codeMat 161) (codeMat 282) (codeMat 28) = codeMat 132 := by
      unfold actionA
      rw [step99o34s3_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 28 * (codeMat 267 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o34_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 20 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 20 (by decide)
    have hact : actionA (codeMat 161) (codeMat 282) (codeMat 20) = codeMat 68 := by
      unfold actionA
      rw [step99o34s3_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 20 * (codeMat 267 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o34_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 196 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 196 (by decide)
    have hact : actionA (codeMat 161) (codeMat 282) (codeMat 196) = codeMat 20 := by
      unfold actionA
      rw [step99o34s3_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 196 * (codeMat 267 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o34_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 128 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 128 (by decide)
    have hact : actionA (codeMat 161) (codeMat 282) (codeMat 128) = codeMat 8 := by
      unfold actionA
      rw [step99o34s3_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 128 * (codeMat 267 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o34_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 3 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 3 (by decide)
    have hact : actionA (codeMat 161) (codeMat 282) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [step99o34s3_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 3 * (codeMat 267 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o34_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 282) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step99o34s3_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 267 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o34_codeMat_mem_actionW_of_witness hw hact

theorem step99o34s3Dispatch :
    QuotientRankAtLeast (o34SourceU ⟨3, by omega⟩) 12 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 282 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 282) orbit11W) 12 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 282) hP hQ orbit11W 12 orbit11_lb12
  have hMono : QuotientRankAtLeast step99o34ActualSource3 12 :=
    quotientRankAtLeast_mono step99o34s3_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o34s3_sourceU_le hMono

-- Source 4 (row 11): orbit 2, lb 6
def step99o34ActualSource4 : Submodule F2 Mat3 := spanCodes [256, 160, 64, 16, 8, 4, 2, 1]

private theorem step99o34s4_sourceU_le :
    (o34SourceU ⟨4, by omega⟩) ≤ step99o34ActualSource4 := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 160, 64, 16, 8, 4, 2, 1] (step99o34MatrixCodeNat M) = true := by
    change M ∈ kerEvalFunc (codeMat 128 + codeMat 32) at hM
    change evalFunc (codeMat 128 + codeMat 32) M = 0 at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] (step99o34MatrixCodeNat M) hbool
  rwa [step99o34_codeMat_matrixCode] at hspan

private theorem step99o34s4_contain :
    step99o34ActualSource4 ≤ flatW_2 := by
  apply step99o34_spanCodes_le_of_gens [256, 160, 64, 16, 8, 4, 2, 1] flatW_2
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 256 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 160 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 64 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 16 (by decide)
  · subst h4
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 8 (by decide)
  · subst h5
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 4 (by decide)
  · subst h6
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 2 (by decide)
  · subst h7
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 1 (by decide)

theorem step99o34s4Dispatch :
    QuotientRankAtLeast (o34SourceU ⟨4, by omega⟩) 6 :=
  quotientRankAtLeast_mono (le_trans step99o34s4_sourceU_le step99o34s4_contain) flatSeed_2

theorem step99o34_all_dispatch (i : Fin 5) :
    QuotientRankAtLeast (o34SourceU i) (o34SourceLb i) := by
  fin_cases i
  · exact step99o34s0Dispatch
  · exact step99o34s1Dispatch
  · exact step99o34s2Dispatch
  · exact step99o34s3Dispatch
  · exact step99o34s4Dispatch

theorem step99_orbit34_lb14_unconditional :
    QuotientRankAtLeast o34W 14 :=
  o34Lb14 step99o34_all_dispatch

end QiushiMatmul
