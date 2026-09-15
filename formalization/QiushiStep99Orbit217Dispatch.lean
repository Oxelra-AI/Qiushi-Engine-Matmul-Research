import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbit10FP
import QiushiOrbit14FP
import QiushiOrbitTransport
import QiushiStep98Orbit217Consumer
import QiushiStep99Orbit56Dispatch
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiTransposeTransport

set_option maxHeartbeats 800000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem step99o217_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step99o217MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step99o217_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step99o217MatrixCodeNat M) = M := by decide

lemma step99o217_codeMat_matrixCode (M : Mat3) :
    codeMat (step99o217MatrixCodeNat M) = M :=
  step99o217_codeMat_matrixCode_all M

private theorem step99o217_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step99o217_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

private theorem step99o217_codeMat_mem_transposeW_of_witness
    {V : Submodule F2 Mat3} {pre tpre : Nat}
    (h_mem : codeMat tpre ∈ V)
    (h_trans : (codeMat tpre : Mat3).transpose = codeMat pre) :
    codeMat pre ∈ transposeW V := by
  change ∃ X, X ∈ V ∧ transposeLinearMap X = codeMat pre
  exact ⟨codeMat tpre, h_mem, h_trans⟩

-- Source 0 (row 1): orbit 65, lb 15
def step99o217ActualSource0 : Submodule F2 Mat3 := spanCodes [272, 132, 68, 36, 10, 1]

private theorem step99o217s0_sourceU_le :
    (o217SourceU ⟨0, by omega⟩) ≤ step99o217ActualSource0 := by
  intro M hM
  have hbool : spanContainsCodeCore [272, 132, 68, 36, 10, 1] (step99o217MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 272) ⊓ kerEvalFunc (codeMat 148 + codeMat 112)) ⊓ kerEvalFunc (codeMat 10)) at hM
    change ((evalFunc (codeMat 272) M = 0 ∧ evalFunc (codeMat 148 + codeMat 112) M = 0) ∧ evalFunc (codeMat 10) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 132, 68, 36, 10, 1] (step99o217MatrixCodeNat M) hbool
  rwa [step99o217_codeMat_matrixCode] at hspan

private theorem step99o217s0_QtInv :
    (codeMat 409 : Mat3).transpose⁻¹ = (codeMat 473 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 409 : Mat3).transpose * (codeMat 473 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o217s0_targetSpan_le_action :
    step99o217ActualSource0 ≤ actionW (codeMat 311) (codeMat 409) o65W := by
  apply step99o217_spanCodes_le_of_gens [272, 132, 68, 36, 10, 1]
    (actionW (codeMat 311) (codeMat 409) o65W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 176 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 176 (by decide)
    have hact : actionA (codeMat 311) (codeMat 409) (codeMat 176) = codeMat 272 := by
      unfold actionA
      rw [step99o217s0_QtInv]
      show (codeMat 311 : Mat3).transpose * codeMat 176 * (codeMat 473 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 420 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 420 (by decide)
    have hact : actionA (codeMat 311) (codeMat 409) (codeMat 420) = codeMat 132 := by
      unfold actionA
      rw [step99o217s0_QtInv]
      show (codeMat 311 : Mat3).transpose * codeMat 420 * (codeMat 473 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 228 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 228 (by decide)
    have hact : actionA (codeMat 311) (codeMat 409) (codeMat 228) = codeMat 68 := by
      unfold actionA
      rw [step99o217s0_QtInv]
      show (codeMat 311 : Mat3).transpose * codeMat 228 * (codeMat 473 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 260 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 260 (by decide)
    have hact : actionA (codeMat 311) (codeMat 409) (codeMat 260) = codeMat 36 := by
      unfold actionA
      rw [step99o217s0_QtInv]
      show (codeMat 311 : Mat3).transpose * codeMat 260 * (codeMat 473 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 238 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 238 (by decide)
    have hact : actionA (codeMat 311) (codeMat 409) (codeMat 238) = codeMat 10 := by
      unfold actionA
      rw [step99o217s0_QtInv]
      show (codeMat 311 : Mat3).transpose * codeMat 238 * (codeMat 473 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 27 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 27 (by decide)
    have hact : actionA (codeMat 311) (codeMat 409) (codeMat 27) = codeMat 1 := by
      unfold actionA
      rw [step99o217s0_QtInv]
      show (codeMat 311 : Mat3).transpose * codeMat 27 * (codeMat 473 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact

theorem step99o217s0Dispatch :
    QuotientRankAtLeast (o217SourceU ⟨0, by omega⟩) 15 := by
  have hP : Invertible (codeMat 311 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 409 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 311) (codeMat 409) o65W) 15 :=
    @quotientRankAtLeast_action (codeMat 311) (codeMat 409) hP hQ o65W 15 step99_orbit65_lb15_unconditional
  have hMono : QuotientRankAtLeast step99o217ActualSource0 15 :=
    quotientRankAtLeast_mono step99o217s0_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o217s0_sourceU_le hMono

-- Source 1 (row 2): orbit 69, lb 15
def step99o217ActualSource1 : Submodule F2 Mat3 := spanCodes [274, 132, 70, 38, 10, 1]

private theorem step99o217s1_sourceU_le :
    (o217SourceU ⟨1, by omega⟩) ≤ step99o217ActualSource1 := by
  intro M hM
  have hbool : spanContainsCodeCore [274, 132, 70, 38, 10, 1] (step99o217MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 272) ⊓ kerEvalFunc (codeMat 148 + codeMat 10)) ⊓ kerEvalFunc (codeMat 112 + codeMat 10)) at hM
    change ((evalFunc (codeMat 272) M = 0 ∧ evalFunc (codeMat 148 + codeMat 10) M = 0) ∧ evalFunc (codeMat 112 + codeMat 10) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [274, 132, 70, 38, 10, 1] (step99o217MatrixCodeNat M) hbool
  rwa [step99o217_codeMat_matrixCode] at hspan

private theorem step99o217s1_QtInv :
    (codeMat 482 : Mat3).transpose⁻¹ = (codeMat 143 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 482 : Mat3).transpose * (codeMat 143 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o217s1_targetSpan_le_action :
    step99o217ActualSource1 ≤ actionW (codeMat 93) (codeMat 482) o69W := by
  apply step99o217_spanCodes_le_of_gens [274, 132, 70, 38, 10, 1]
    (actionW (codeMat 93) (codeMat 482) o69W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 430 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 430 (by decide)
    have hact : actionA (codeMat 93) (codeMat 482) (codeMat 430) = codeMat 274 := by
      unfold actionA
      rw [step99o217s1_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 430 * (codeMat 143 : Mat3).transpose = codeMat 274
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 197 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 197 (by decide)
    have hact : actionA (codeMat 93) (codeMat 482) (codeMat 197) = codeMat 132 := by
      unfold actionA
      rw [step99o217s1_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 197 * (codeMat 143 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 452 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 452 (by decide)
    have hact : actionA (codeMat 93) (codeMat 482) (codeMat 452) = codeMat 70 := by
      unfold actionA
      rw [step99o217s1_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 452 * (codeMat 143 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 368 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 368 (by decide)
    have hact : actionA (codeMat 93) (codeMat 482) (codeMat 368) = codeMat 38 := by
      unfold actionA
      rw [step99o217s1_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 368 * (codeMat 143 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 96 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 96 (by decide)
    have hact : actionA (codeMat 93) (codeMat 482) (codeMat 96) = codeMat 10 := by
      unfold actionA
      rw [step99o217s1_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 96 * (codeMat 143 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 256 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 256 (by decide)
    have hact : actionA (codeMat 93) (codeMat 482) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step99o217s1_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 256 * (codeMat 143 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact

theorem step99o217s1Dispatch :
    QuotientRankAtLeast (o217SourceU ⟨1, by omega⟩) 15 := by
  have hP : Invertible (codeMat 93 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 482 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 93) (codeMat 482) o69W) 15 :=
    @quotientRankAtLeast_action (codeMat 93) (codeMat 482) hP hQ o69W 15 step99_orbit69_lb15_unconditional
  have hMono : QuotientRankAtLeast step99o217ActualSource1 15 :=
    quotientRankAtLeast_mono step99o217s1_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o217s1_sourceU_le hMono

-- Source 2 (row 3): orbit 56, lb 14
def step99o217ActualSource2 : Submodule F2 Mat3 := spanCodes [304, 128, 96, 10, 4, 1]

private theorem step99o217s2_sourceU_le :
    (o217SourceU ⟨2, by omega⟩) ≤ step99o217ActualSource2 := by
  intro M hM
  have hbool : spanContainsCodeCore [304, 128, 96, 10, 4, 1] (step99o217MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 272) ⊓ kerEvalFunc (codeMat 112)) ⊓ kerEvalFunc (codeMat 10)) at hM
    change ((evalFunc (codeMat 272) M = 0 ∧ evalFunc (codeMat 112) M = 0) ∧ evalFunc (codeMat 10) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [304, 128, 96, 10, 4, 1] (step99o217MatrixCodeNat M) hbool
  rwa [step99o217_codeMat_matrixCode] at hspan

private theorem step99o217s2_QtInv :
    (codeMat 183 : Mat3).transpose⁻¹ = (codeMat 419 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 183 : Mat3).transpose * (codeMat 419 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o217s2_targetSpan_le_action :
    step99o217ActualSource2 ≤ actionW (codeMat 409) (codeMat 183) o56W := by
  apply step99o217_spanCodes_le_of_gens [304, 128, 96, 10, 4, 1]
    (actionW (codeMat 409) (codeMat 183) o56W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 255 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 255 (by decide)
    have hact : actionA (codeMat 409) (codeMat 183) (codeMat 255) = codeMat 304 := by
      unfold actionA
      rw [step99o217s2_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 255 * (codeMat 419 : Mat3).transpose = codeMat 304
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 511 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 511 (by decide)
    have hact : actionA (codeMat 409) (codeMat 183) (codeMat 511) = codeMat 128 := by
      unfold actionA
      rw [step99o217s2_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 511 * (codeMat 419 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 82 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 82 (by decide)
    have hact : actionA (codeMat 409) (codeMat 183) (codeMat 82) = codeMat 96 := by
      unfold actionA
      rw [step99o217s2_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 82 * (codeMat 419 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 14 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 14 (by decide)
    have hact : actionA (codeMat 409) (codeMat 183) (codeMat 14) = codeMat 10 := by
      unfold actionA
      rw [step99o217s2_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 14 * (codeMat 419 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 409) (codeMat 183) (codeMat 3) = codeMat 4 := by
      unfold actionA
      rw [step99o217s2_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 3 * (codeMat 419 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 409) (codeMat 183) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step99o217s2_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 1 * (codeMat 419 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact

theorem step99o217s2Dispatch :
    QuotientRankAtLeast (o217SourceU ⟨2, by omega⟩) 14 := by
  have hP : Invertible (codeMat 409 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 183 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 409) (codeMat 183) o56W) 14 :=
    @quotientRankAtLeast_action (codeMat 409) (codeMat 183) hP hQ o56W 14 step99_orbit56_lb14_unconditional
  have hMono : QuotientRankAtLeast step99o217ActualSource2 14 :=
    quotientRankAtLeast_mono step99o217s2_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o217s2_sourceU_le hMono

-- Source 3 (row 4): orbit 56, lb 14
def step99o217ActualSource3 : Submodule F2 Mat3 := spanCodes [288, 132, 96, 20, 10, 1]

private theorem step99o217s3_sourceU_le :
    (o217SourceU ⟨3, by omega⟩) ≤ step99o217ActualSource3 := by
  intro M hM
  have hbool : spanContainsCodeCore [288, 132, 96, 20, 10, 1] (step99o217MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 272 + codeMat 112) ⊓ kerEvalFunc (codeMat 148)) ⊓ kerEvalFunc (codeMat 10)) at hM
    change ((evalFunc (codeMat 272 + codeMat 112) M = 0 ∧ evalFunc (codeMat 148) M = 0) ∧ evalFunc (codeMat 10) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 132, 96, 20, 10, 1] (step99o217MatrixCodeNat M) hbool
  rwa [step99o217_codeMat_matrixCode] at hspan

private theorem step99o217s3_QtInv :
    (codeMat 116 : Mat3).transpose⁻¹ = (codeMat 92 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 116 : Mat3).transpose * (codeMat 92 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o217s3_targetSpan_le_action :
    step99o217ActualSource3 ≤ actionW (codeMat 94) (codeMat 116) o56W := by
  apply step99o217_spanCodes_le_of_gens [288, 132, 96, 20, 10, 1]
    (actionW (codeMat 94) (codeMat 116) o56W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 3 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 94) (codeMat 116) (codeMat 3) = codeMat 288 := by
      unfold actionA
      rw [step99o217s3_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 3 * (codeMat 92 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 82 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 82 (by decide)
    have hact : actionA (codeMat 94) (codeMat 116) (codeMat 82) = codeMat 132 := by
      unfold actionA
      rw [step99o217s3_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 82 * (codeMat 92 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 508 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 508 (by decide)
    have hact : actionA (codeMat 94) (codeMat 116) (codeMat 508) = codeMat 96 := by
      unfold actionA
      rw [step99o217s3_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 508 * (codeMat 92 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 80 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 80 (by decide)
    have hact : actionA (codeMat 94) (codeMat 116) (codeMat 80) = codeMat 20 := by
      unfold actionA
      rw [step99o217s3_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 80 * (codeMat 92 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 416 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 416 (by decide)
    have hact : actionA (codeMat 94) (codeMat 116) (codeMat 416) = codeMat 10 := by
      unfold actionA
      rw [step99o217s3_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 416 * (codeMat 92 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 256 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 94) (codeMat 116) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step99o217s3_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 256 * (codeMat 92 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact

theorem step99o217s3Dispatch :
    QuotientRankAtLeast (o217SourceU ⟨3, by omega⟩) 14 := by
  have hP : Invertible (codeMat 94 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 116 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 94) (codeMat 116) o56W) 14 :=
    @quotientRankAtLeast_action (codeMat 94) (codeMat 116) hP hQ o56W 14 step99_orbit56_lb14_unconditional
  have hMono : QuotientRankAtLeast step99o217ActualSource3 14 :=
    quotientRankAtLeast_mono step99o217s3_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o217s3_sourceU_le hMono

-- Source 4 (row 6): orbit 56, lb 14
def step99o217ActualSource4 : Submodule F2 Mat3 := spanCodes [276, 132, 64, 32, 10, 1]

private theorem step99o217s4_sourceU_le :
    (o217SourceU ⟨4, by omega⟩) ≤ step99o217ActualSource4 := by
  intro M hM
  have hbool : spanContainsCodeCore [276, 132, 64, 32, 10, 1] (step99o217MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 272) ⊓ kerEvalFunc (codeMat 148)) ⊓ kerEvalFunc (codeMat 10)) at hM
    change ((evalFunc (codeMat 272) M = 0 ∧ evalFunc (codeMat 148) M = 0) ∧ evalFunc (codeMat 10) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [276, 132, 64, 32, 10, 1] (step99o217MatrixCodeNat M) hbool
  rwa [step99o217_codeMat_matrixCode] at hspan

private theorem step99o217s4_QtInv :
    (codeMat 183 : Mat3).transpose⁻¹ = (codeMat 419 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 183 : Mat3).transpose * (codeMat 419 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o217s4_targetSpan_le_transposeAction :
    step99o217ActualSource4 ≤ transposeW (actionW (codeMat 409) (codeMat 183) o56W) := by
  apply step99o217_spanCodes_le_of_gens [276, 132, 64, 32, 10, 1]
    (transposeW (actionW (codeMat 409) (codeMat 183) o56W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    -- g=276, g^T=336; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 173 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 173 (by decide)
    have hact : actionA (codeMat 409) (codeMat 183) (codeMat 173) = codeMat 336 := by
      unfold actionA
      rw [step99o217s4_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 173 * (codeMat 419 : Mat3).transpose = codeMat 336
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 336 ∈ actionW (codeMat 409) (codeMat 183) o56W :=
      step99o217_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 336 : Mat3).transpose = codeMat 276 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h1
    -- g=132, g^T=96; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 82 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 82 (by decide)
    have hact : actionA (codeMat 409) (codeMat 183) (codeMat 82) = codeMat 96 := by
      unfold actionA
      rw [step99o217s4_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 82 * (codeMat 419 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 96 ∈ actionW (codeMat 409) (codeMat 183) o56W :=
      step99o217_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 96 : Mat3).transpose = codeMat 132 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h2
    -- g=64, g^T=4; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 3 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 409) (codeMat 183) (codeMat 3) = codeMat 4 := by
      unfold actionA
      rw [step99o217s4_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 3 * (codeMat 419 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 4 ∈ actionW (codeMat 409) (codeMat 183) o56W :=
      step99o217_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 4 : Mat3).transpose = codeMat 64 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h3
    -- g=32, g^T=128; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 511 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 511 (by decide)
    have hact : actionA (codeMat 409) (codeMat 183) (codeMat 511) = codeMat 128 := by
      unfold actionA
      rw [step99o217s4_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 511 * (codeMat 419 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 128 ∈ actionW (codeMat 409) (codeMat 183) o56W :=
      step99o217_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 128 : Mat3).transpose = codeMat 32 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h4
    -- g=10, g^T=10; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 14 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 14 (by decide)
    have hact : actionA (codeMat 409) (codeMat 183) (codeMat 14) = codeMat 10 := by
      unfold actionA
      rw [step99o217s4_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 14 * (codeMat 419 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 10 ∈ actionW (codeMat 409) (codeMat 183) o56W :=
      step99o217_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 10 : Mat3).transpose = codeMat 10 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h5
    -- g=1, g^T=1; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 1 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 409) (codeMat 183) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step99o217s4_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 1 * (codeMat 419 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 1 ∈ actionW (codeMat 409) (codeMat 183) o56W :=
      step99o217_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 1 : Mat3).transpose = codeMat 1 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_transposeW_of_witness hmemAction htrans

theorem step99o217s4Dispatch :
    QuotientRankAtLeast (o217SourceU ⟨4, by omega⟩) 14 := by
  have hP : Invertible (codeMat 409 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 183 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 409) (codeMat 183) o56W) 14 :=
    @quotientRankAtLeast_action (codeMat 409) (codeMat 183) hP hQ o56W 14 step99_orbit56_lb14_unconditional
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 409) (codeMat 183) o56W)) 14 :=
    quotientRankAtLeast_transpose hAct
  have hMono : QuotientRankAtLeast step99o217ActualSource4 14 :=
    quotientRankAtLeast_mono step99o217s4_targetSpan_le_transposeAction hT
  exact quotientRankAtLeast_mono step99o217s4_sourceU_le hMono

-- Source 5 (row 7): orbit 56, lb 14
def step99o217ActualSource5 : Submodule F2 Mat3 := spanCodes [260, 132, 80, 48, 10, 1]

private theorem step99o217s5_sourceU_le :
    (o217SourceU ⟨5, by omega⟩) ≤ step99o217ActualSource5 := by
  intro M hM
  have hbool : spanContainsCodeCore [260, 132, 80, 48, 10, 1] (step99o217MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 272 + codeMat 148) ⊓ kerEvalFunc (codeMat 112)) ⊓ kerEvalFunc (codeMat 10)) at hM
    change ((evalFunc (codeMat 272 + codeMat 148) M = 0 ∧ evalFunc (codeMat 112) M = 0) ∧ evalFunc (codeMat 10) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 132, 80, 48, 10, 1] (step99o217MatrixCodeNat M) hbool
  rwa [step99o217_codeMat_matrixCode] at hspan

private theorem step99o217s5_QtInv :
    (codeMat 116 : Mat3).transpose⁻¹ = (codeMat 92 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 116 : Mat3).transpose * (codeMat 92 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o217s5_targetSpan_le_transposeAction :
    step99o217ActualSource5 ≤ transposeW (actionW (codeMat 94) (codeMat 116) o56W) := by
  apply step99o217_spanCodes_le_of_gens [260, 132, 80, 48, 10, 1]
    (transposeW (actionW (codeMat 94) (codeMat 116) o56W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    -- g=260, g^T=320; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 511 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 511 (by decide)
    have hact : actionA (codeMat 94) (codeMat 116) (codeMat 511) = codeMat 320 := by
      unfold actionA
      rw [step99o217s5_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 511 * (codeMat 92 : Mat3).transpose = codeMat 320
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 320 ∈ actionW (codeMat 94) (codeMat 116) o56W :=
      step99o217_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 320 : Mat3).transpose = codeMat 260 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h1
    -- g=132, g^T=96; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 508 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 508 (by decide)
    have hact : actionA (codeMat 94) (codeMat 116) (codeMat 508) = codeMat 96 := by
      unfold actionA
      rw [step99o217s5_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 508 * (codeMat 92 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 96 ∈ actionW (codeMat 94) (codeMat 116) o56W :=
      step99o217_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 96 : Mat3).transpose = codeMat 132 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h2
    -- g=80, g^T=20; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 80 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 80 (by decide)
    have hact : actionA (codeMat 94) (codeMat 116) (codeMat 80) = codeMat 20 := by
      unfold actionA
      rw [step99o217s5_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 80 * (codeMat 92 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 20 ∈ actionW (codeMat 94) (codeMat 116) o56W :=
      step99o217_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 20 : Mat3).transpose = codeMat 80 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h3
    -- g=48, g^T=144; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 2 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 94) (codeMat 116) (codeMat 2) = codeMat 144 := by
      unfold actionA
      rw [step99o217s5_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 2 * (codeMat 92 : Mat3).transpose = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 144 ∈ actionW (codeMat 94) (codeMat 116) o56W :=
      step99o217_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 144 : Mat3).transpose = codeMat 48 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h4
    -- g=10, g^T=10; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 416 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 416 (by decide)
    have hact : actionA (codeMat 94) (codeMat 116) (codeMat 416) = codeMat 10 := by
      unfold actionA
      rw [step99o217s5_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 416 * (codeMat 92 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 10 ∈ actionW (codeMat 94) (codeMat 116) o56W :=
      step99o217_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 10 : Mat3).transpose = codeMat 10 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h5
    -- g=1, g^T=1; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 256 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 94) (codeMat 116) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step99o217s5_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 256 * (codeMat 92 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 1 ∈ actionW (codeMat 94) (codeMat 116) o56W :=
      step99o217_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 1 : Mat3).transpose = codeMat 1 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_transposeW_of_witness hmemAction htrans

theorem step99o217s5Dispatch :
    QuotientRankAtLeast (o217SourceU ⟨5, by omega⟩) 14 := by
  have hP : Invertible (codeMat 94 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 116 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 94) (codeMat 116) o56W) 14 :=
    @quotientRankAtLeast_action (codeMat 94) (codeMat 116) hP hQ o56W 14 step99_orbit56_lb14_unconditional
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 94) (codeMat 116) o56W)) 14 :=
    quotientRankAtLeast_transpose hAct
  have hMono : QuotientRankAtLeast step99o217ActualSource5 14 :=
    quotientRankAtLeast_mono step99o217s5_targetSpan_le_transposeAction hT
  exact quotientRankAtLeast_mono step99o217s5_sourceU_le hMono

-- Source 6 (row 15): orbit 10, lb 12
def step99o217ActualSource6 : Submodule F2 Mat3 := spanCodes [292, 132, 96, 16, 8, 2, 1]

private theorem step99o217s6_sourceU_le :
    (o217SourceU ⟨6, by omega⟩) ≤ step99o217ActualSource6 := by
  intro M hM
  have hbool : spanContainsCodeCore [292, 132, 96, 16, 8, 2, 1] (step99o217MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 272 + codeMat 112) ⊓ kerEvalFunc (codeMat 148 + codeMat 112)) at hM
    change (evalFunc (codeMat 272 + codeMat 112) M = 0 ∧ evalFunc (codeMat 148 + codeMat 112) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [292, 132, 96, 16, 8, 2, 1] (step99o217MatrixCodeNat M) hbool
  rwa [step99o217_codeMat_matrixCode] at hspan

private theorem step99o217s6_QtInv :
    (codeMat 309 : Mat3).transpose⁻¹ = (codeMat 309 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 309 : Mat3).transpose * (codeMat 309 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o217s6_targetSpan_le_action :
    step99o217ActualSource6 ≤ actionW (codeMat 266) (codeMat 309) orbit10W := by
  apply step99o217_spanCodes_le_of_gens [292, 132, 96, 16, 8, 2, 1]
    (actionW (codeMat 266) (codeMat 309) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 511 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 511 (by decide)
    have hact : actionA (codeMat 266) (codeMat 309) (codeMat 511) = codeMat 292 := by
      unfold actionA
      rw [step99o217s6_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 511 * (codeMat 309 : Mat3).transpose = codeMat 292
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 184 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 184 (by decide)
    have hact : actionA (codeMat 266) (codeMat 309) (codeMat 184) = codeMat 132 := by
      unfold actionA
      rw [step99o217s6_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 184 * (codeMat 309 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 71 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 71 (by decide)
    have hact : actionA (codeMat 266) (codeMat 309) (codeMat 71) = codeMat 96 := by
      unfold actionA
      rw [step99o217s6_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 71 * (codeMat 309 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 309) (codeMat 2) = codeMat 16 := by
      unfold actionA
      rw [step99o217s6_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 309 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 309) (codeMat 1) = codeMat 8 := by
      unfold actionA
      rw [step99o217s6_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 309 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 309) (codeMat 16) = codeMat 2 := by
      unfold actionA
      rw [step99o217s6_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 309 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 309) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step99o217s6_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 309 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact

theorem step99o217s6Dispatch :
    QuotientRankAtLeast (o217SourceU ⟨6, by omega⟩) 12 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 309 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 309) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 309) hP hQ orbit10W 12 orbit10_lb12
  have hMono : QuotientRankAtLeast step99o217ActualSource6 12 :=
    quotientRankAtLeast_mono step99o217s6_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o217s6_sourceU_le hMono

-- Source 7 (row 20): orbit 10, lb 12
def step99o217ActualSource7 : Submodule F2 Mat3 := spanCodes [272, 130, 66, 34, 10, 6, 1]

private theorem step99o217s7_sourceU_le :
    (o217SourceU ⟨7, by omega⟩) ≤ step99o217ActualSource7 := by
  intro M hM
  have hbool : spanContainsCodeCore [272, 130, 66, 34, 10, 6, 1] (step99o217MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 272) ⊓ kerEvalFunc (codeMat 148 + codeMat 112 + codeMat 10)) at hM
    change (evalFunc (codeMat 272) M = 0 ∧ evalFunc (codeMat 148 + codeMat 112 + codeMat 10) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 130, 66, 34, 10, 6, 1] (step99o217MatrixCodeNat M) hbool
  rwa [step99o217_codeMat_matrixCode] at hspan

private theorem step99o217s7_QtInv :
    (codeMat 444 : Mat3).transpose⁻¹ = (codeMat 110 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 444 : Mat3).transpose * (codeMat 110 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o217s7_targetSpan_le_action :
    step99o217ActualSource7 ≤ actionW (codeMat 270) (codeMat 444) orbit10W := by
  apply step99o217_spanCodes_le_of_gens [272, 130, 66, 34, 10, 6, 1]
    (actionW (codeMat 270) (codeMat 444) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 70 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 70 (by decide)
    have hact : actionA (codeMat 270) (codeMat 444) (codeMat 70) = codeMat 272 := by
      unfold actionA
      rw [step99o217s7_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 70 * (codeMat 110 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 432 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 432 (by decide)
    have hact : actionA (codeMat 270) (codeMat 444) (codeMat 432) = codeMat 130 := by
      unfold actionA
      rw [step99o217s7_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 432 * (codeMat 110 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 176 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 176 (by decide)
    have hact : actionA (codeMat 270) (codeMat 444) (codeMat 176) = codeMat 66 := by
      unfold actionA
      rw [step99o217s7_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 176 * (codeMat 110 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 503 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 503 (by decide)
    have hact : actionA (codeMat 270) (codeMat 444) (codeMat 503) = codeMat 34 := by
      unfold actionA
      rw [step99o217s7_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 503 * (codeMat 110 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 178 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 178 (by decide)
    have hact : actionA (codeMat 270) (codeMat 444) (codeMat 178) = codeMat 10 := by
      unfold actionA
      rw [step99o217s7_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 178 * (codeMat 110 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 270) (codeMat 444) (codeMat 8) = codeMat 6 := by
      unfold actionA
      rw [step99o217s7_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 8 * (codeMat 110 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 270) (codeMat 444) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step99o217s7_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 16 * (codeMat 110 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact

theorem step99o217s7Dispatch :
    QuotientRankAtLeast (o217SourceU ⟨7, by omega⟩) 12 := by
  have hP : Invertible (codeMat 270 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 444 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 270) (codeMat 444) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 270) (codeMat 444) hP hQ orbit10W 12 orbit10_lb12
  have hMono : QuotientRankAtLeast step99o217ActualSource7 12 :=
    quotientRankAtLeast_mono step99o217s7_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o217s7_sourceU_le hMono

-- Source 8 (row 32): orbit 14, lb 12
def step99o217ActualSource8 : Submodule F2 Mat3 := spanCodes [256, 132, 66, 34, 22, 10, 1]

private theorem step99o217s8_sourceU_le :
    (o217SourceU ⟨8, by omega⟩) ≤ step99o217ActualSource8 := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 132, 66, 34, 22, 10, 1] (step99o217MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 148) ⊓ kerEvalFunc (codeMat 112 + codeMat 10)) at hM
    change (evalFunc (codeMat 148) M = 0 ∧ evalFunc (codeMat 112 + codeMat 10) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 132, 66, 34, 22, 10, 1] (step99o217MatrixCodeNat M) hbool
  rwa [step99o217_codeMat_matrixCode] at hspan

private theorem step99o217s8_QtInv :
    (codeMat 412 : Mat3).transpose⁻¹ = (codeMat 111 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 412 : Mat3).transpose * (codeMat 111 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o217s8_targetSpan_le_action :
    step99o217ActualSource8 ≤ actionW (codeMat 478) (codeMat 412) orbit14W := by
  apply step99o217_spanCodes_le_of_gens [256, 132, 66, 34, 22, 10, 1]
    (actionW (codeMat 478) (codeMat 412) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 478) (codeMat 412) (codeMat 360) = codeMat 256 := by
      unfold actionA
      rw [step99o217s8_QtInv]
      show (codeMat 478 : Mat3).transpose * codeMat 360 * (codeMat 111 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 245 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 245 (by decide)
    have hact : actionA (codeMat 478) (codeMat 412) (codeMat 245) = codeMat 132 := by
      unfold actionA
      rw [step99o217s8_QtInv]
      show (codeMat 478 : Mat3).transpose * codeMat 245 * (codeMat 111 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 278 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 278 (by decide)
    have hact : actionA (codeMat 478) (codeMat 412) (codeMat 278) = codeMat 66 := by
      unfold actionA
      rw [step99o217s8_QtInv]
      show (codeMat 478 : Mat3).transpose * codeMat 278 * (codeMat 111 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 235 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 235 (by decide)
    have hact : actionA (codeMat 478) (codeMat 412) (codeMat 235) = codeMat 34 := by
      unfold actionA
      rw [step99o217s8_QtInv]
      show (codeMat 478 : Mat3).transpose * codeMat 235 * (codeMat 111 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 373 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 373 (by decide)
    have hact : actionA (codeMat 478) (codeMat 412) (codeMat 373) = codeMat 22 := by
      unfold actionA
      rw [step99o217s8_QtInv]
      show (codeMat 478 : Mat3).transpose * codeMat 373 * (codeMat 111 : Mat3).transpose = codeMat 22
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 276 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 276 (by decide)
    have hact : actionA (codeMat 478) (codeMat 412) (codeMat 276) = codeMat 10 := by
      unfold actionA
      rw [step99o217s8_QtInv]
      show (codeMat 478 : Mat3).transpose * codeMat 276 * (codeMat 111 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 130 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 130 (by decide)
    have hact : actionA (codeMat 478) (codeMat 412) (codeMat 130) = codeMat 1 := by
      unfold actionA
      rw [step99o217s8_QtInv]
      show (codeMat 478 : Mat3).transpose * codeMat 130 * (codeMat 111 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact

theorem step99o217s8Dispatch :
    QuotientRankAtLeast (o217SourceU ⟨8, by omega⟩) 12 := by
  have hP : Invertible (codeMat 478 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 412 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 478) (codeMat 412) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 478) (codeMat 412) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step99o217ActualSource8 12 :=
    quotientRankAtLeast_mono step99o217s8_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o217s8_sourceU_le hMono

-- Source 9 (row 36): orbit 14, lb 12
def step99o217ActualSource9 : Submodule F2 Mat3 := spanCodes [256, 130, 82, 50, 10, 6, 1]

private theorem step99o217s9_sourceU_le :
    (o217SourceU ⟨9, by omega⟩) ≤ step99o217ActualSource9 := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 130, 82, 50, 10, 6, 1] (step99o217MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 148 + codeMat 10) ⊓ kerEvalFunc (codeMat 112)) at hM
    change (evalFunc (codeMat 148 + codeMat 10) M = 0 ∧ evalFunc (codeMat 112) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 130, 82, 50, 10, 6, 1] (step99o217MatrixCodeNat M) hbool
  rwa [step99o217_codeMat_matrixCode] at hspan

private theorem step99o217s9_QtInv :
    (codeMat 415 : Mat3).transpose⁻¹ = (codeMat 253 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 415 : Mat3).transpose * (codeMat 253 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o217s9_targetSpan_le_action :
    step99o217ActualSource9 ≤ actionW (codeMat 473) (codeMat 415) orbit14W := by
  apply step99o217_spanCodes_le_of_gens [256, 130, 82, 50, 10, 6, 1]
    (actionW (codeMat 473) (codeMat 415) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 473) (codeMat 415) (codeMat 360) = codeMat 256 := by
      unfold actionA
      rw [step99o217s9_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 360 * (codeMat 253 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 511 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 511 (by decide)
    have hact : actionA (codeMat 473) (codeMat 415) (codeMat 511) = codeMat 130 := by
      unfold actionA
      rw [step99o217s9_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 511 * (codeMat 253 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 224 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 224 (by decide)
    have hact : actionA (codeMat 473) (codeMat 415) (codeMat 224) = codeMat 82 := by
      unfold actionA
      rw [step99o217s9_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 224 * (codeMat 253 : Mat3).transpose = codeMat 82
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 21 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 21 (by decide)
    have hact : actionA (codeMat 473) (codeMat 415) (codeMat 21) = codeMat 50 := by
      unfold actionA
      rw [step99o217s9_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 21 * (codeMat 253 : Mat3).transpose = codeMat 50
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 28 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 28 (by decide)
    have hact : actionA (codeMat 473) (codeMat 415) (codeMat 28) = codeMat 10 := by
      unfold actionA
      rw [step99o217s9_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 28 * (codeMat 253 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 473) (codeMat 415) (codeMat 2) = codeMat 6 := by
      unfold actionA
      rw [step99o217s9_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 2 * (codeMat 253 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 473) (codeMat 415) (codeMat 3) = codeMat 1 := by
      unfold actionA
      rw [step99o217s9_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 3 * (codeMat 253 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact

theorem step99o217s9Dispatch :
    QuotientRankAtLeast (o217SourceU ⟨9, by omega⟩) 12 := by
  have hP : Invertible (codeMat 473 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 415 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 473) (codeMat 415) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 473) (codeMat 415) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step99o217ActualSource9 12 :=
    quotientRankAtLeast_mono step99o217s9_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o217s9_sourceU_le hMono

-- Source 10 (row 37): orbit 14, lb 12
def step99o217ActualSource10 : Submodule F2 Mat3 := spanCodes [258, 132, 64, 32, 22, 10, 1]

private theorem step99o217s10_sourceU_le :
    (o217SourceU ⟨10, by omega⟩) ≤ step99o217ActualSource10 := by
  intro M hM
  have hbool : spanContainsCodeCore [258, 132, 64, 32, 22, 10, 1] (step99o217MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 272 + codeMat 10) ⊓ kerEvalFunc (codeMat 148)) at hM
    change (evalFunc (codeMat 272 + codeMat 10) M = 0 ∧ evalFunc (codeMat 148) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 132, 64, 32, 22, 10, 1] (step99o217MatrixCodeNat M) hbool
  rwa [step99o217_codeMat_matrixCode] at hspan

private theorem step99o217s10_QtInv :
    (codeMat 407 : Mat3).transpose⁻¹ = (codeMat 405 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 407 : Mat3).transpose * (codeMat 405 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o217s10_targetSpan_le_action :
    step99o217ActualSource10 ≤ actionW (codeMat 421) (codeMat 407) orbit14W := by
  apply step99o217_spanCodes_le_of_gens [258, 132, 64, 32, 22, 10, 1]
    (actionW (codeMat 421) (codeMat 407) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 23 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 23 (by decide)
    have hact : actionA (codeMat 421) (codeMat 407) (codeMat 23) = codeMat 258 := by
      unfold actionA
      rw [step99o217s10_QtInv]
      show (codeMat 421 : Mat3).transpose * codeMat 23 * (codeMat 405 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 21 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 21 (by decide)
    have hact : actionA (codeMat 421) (codeMat 407) (codeMat 21) = codeMat 132 := by
      unfold actionA
      rw [step99o217s10_QtInv]
      show (codeMat 421 : Mat3).transpose * codeMat 21 * (codeMat 405 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 421) (codeMat 407) (codeMat 8) = codeMat 64 := by
      unfold actionA
      rw [step99o217s10_QtInv]
      show (codeMat 421 : Mat3).transpose * codeMat 8 * (codeMat 405 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 421) (codeMat 407) (codeMat 360) = codeMat 32 := by
      unfold actionA
      rw [step99o217s10_QtInv]
      show (codeMat 421 : Mat3).transpose * codeMat 360 * (codeMat 405 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 490 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 490 (by decide)
    have hact : actionA (codeMat 421) (codeMat 407) (codeMat 490) = codeMat 22 := by
      unfold actionA
      rw [step99o217s10_QtInv]
      show (codeMat 421 : Mat3).transpose * codeMat 490 * (codeMat 405 : Mat3).transpose = codeMat 22
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 119 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 119 (by decide)
    have hact : actionA (codeMat 421) (codeMat 407) (codeMat 119) = codeMat 10 := by
      unfold actionA
      rw [step99o217s10_QtInv]
      show (codeMat 421 : Mat3).transpose * codeMat 119 * (codeMat 405 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 9 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 9 (by decide)
    have hact : actionA (codeMat 421) (codeMat 407) (codeMat 9) = codeMat 1 := by
      unfold actionA
      rw [step99o217s10_QtInv]
      show (codeMat 421 : Mat3).transpose * codeMat 9 * (codeMat 405 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact

theorem step99o217s10Dispatch :
    QuotientRankAtLeast (o217SourceU ⟨10, by omega⟩) 12 := by
  have hP : Invertible (codeMat 421 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 407 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 421) (codeMat 407) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 421) (codeMat 407) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step99o217ActualSource10 12 :=
    quotientRankAtLeast_mono step99o217s10_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o217s10_sourceU_le hMono

-- Source 11 (row 40): orbit 14, lb 12
def step99o217ActualSource11 : Submodule F2 Mat3 := spanCodes [258, 128, 82, 50, 10, 4, 1]

private theorem step99o217s11_sourceU_le :
    (o217SourceU ⟨11, by omega⟩) ≤ step99o217ActualSource11 := by
  intro M hM
  have hbool : spanContainsCodeCore [258, 128, 82, 50, 10, 4, 1] (step99o217MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 272 + codeMat 10) ⊓ kerEvalFunc (codeMat 112)) at hM
    change (evalFunc (codeMat 272 + codeMat 10) M = 0 ∧ evalFunc (codeMat 112) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 128, 82, 50, 10, 4, 1] (step99o217MatrixCodeNat M) hbool
  rwa [step99o217_codeMat_matrixCode] at hspan

private theorem step99o217s11_QtInv :
    (codeMat 458 : Mat3).transpose⁻¹ = (codeMat 458 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 458 : Mat3).transpose * (codeMat 458 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o217s11_targetSpan_le_action :
    step99o217ActualSource11 ≤ actionW (codeMat 110) (codeMat 458) orbit14W := by
  apply step99o217_spanCodes_le_of_gens [258, 128, 82, 50, 10, 4, 1]
    (actionW (codeMat 110) (codeMat 458) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 110) (codeMat 458) (codeMat 96) = codeMat 258 := by
      unfold actionA
      rw [step99o217s11_QtInv]
      show (codeMat 110 : Mat3).transpose * codeMat 96 * (codeMat 458 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 110) (codeMat 458) (codeMat 360) = codeMat 128 := by
      unfold actionA
      rw [step99o217s11_QtInv]
      show (codeMat 110 : Mat3).transpose * codeMat 360 * (codeMat 458 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 413 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 413 (by decide)
    have hact : actionA (codeMat 110) (codeMat 458) (codeMat 413) = codeMat 82 := by
      unfold actionA
      rw [step99o217s11_QtInv]
      show (codeMat 110 : Mat3).transpose * codeMat 413 * (codeMat 458 : Mat3).transpose = codeMat 82
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 265 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 265 (by decide)
    have hact : actionA (codeMat 110) (codeMat 458) (codeMat 265) = codeMat 50 := by
      unfold actionA
      rw [step99o217s11_QtInv]
      show (codeMat 110 : Mat3).transpose * codeMat 265 * (codeMat 458 : Mat3).transpose = codeMat 50
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 246 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 246 (by decide)
    have hact : actionA (codeMat 110) (codeMat 458) (codeMat 246) = codeMat 10 := by
      unfold actionA
      rw [step99o217s11_QtInv]
      show (codeMat 110 : Mat3).transpose * codeMat 246 * (codeMat 458 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 110) (codeMat 458) (codeMat 256) = codeMat 4 := by
      unfold actionA
      rw [step99o217s11_QtInv]
      show (codeMat 110 : Mat3).transpose * codeMat 256 * (codeMat 458 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 110) (codeMat 458) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step99o217s11_QtInv]
      show (codeMat 110 : Mat3).transpose * codeMat 384 * (codeMat 458 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o217_codeMat_mem_actionW_of_witness hw hact

theorem step99o217s11Dispatch :
    QuotientRankAtLeast (o217SourceU ⟨11, by omega⟩) 12 := by
  have hP : Invertible (codeMat 110 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 458 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 110) (codeMat 458) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 110) (codeMat 458) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step99o217ActualSource11 12 :=
    quotientRankAtLeast_mono step99o217s11_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o217s11_sourceU_le hMono

theorem step99o217_all_dispatch (i : Fin 12) :
    QuotientRankAtLeast (o217SourceU i) (o217SourceLb i) := by
  fin_cases i
  · exact step99o217s0Dispatch
  · exact step99o217s1Dispatch
  · exact step99o217s2Dispatch
  · exact step99o217s3Dispatch
  · exact step99o217s4Dispatch
  · exact step99o217s5Dispatch
  · exact step99o217s6Dispatch
  · exact step99o217s7Dispatch
  · exact step99o217s8Dispatch
  · exact step99o217s9Dispatch
  · exact step99o217s10Dispatch
  · exact step99o217s11Dispatch

theorem step99_orbit217_lb16_unconditional :
    QuotientRankAtLeast o217W 16 :=
  o217Lb16 step99o217_all_dispatch

end QiushiMatmul
