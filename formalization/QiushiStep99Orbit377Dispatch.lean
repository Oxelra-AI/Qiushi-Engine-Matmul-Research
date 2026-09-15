import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbit29FP
import QiushiOrbitTransport
import QiushiStep98Orbit377Consumer
import QiushiStep99Orbit231Dispatch
import QiushiStep99Orbit67Dispatch

set_option maxHeartbeats 800000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem step99o377_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step99o377MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step99o377_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step99o377MatrixCodeNat M) = M := by decide

lemma step99o377_codeMat_matrixCode (M : Mat3) :
    codeMat (step99o377MatrixCodeNat M) = M :=
  step99o377_codeMat_matrixCode_all M

private theorem step99o377_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step99o377_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

-- Source 0 (row 6): orbit 29, lb 15
def step99o377ActualSource0 : Submodule F2 Mat3 := spanCodes [160, 68, 16, 8, 2, 1]

private theorem step99o377s0_sourceU_le :
    (o377SourceU ⟨0, by omega⟩) ≤ step99o377ActualSource0 := by
  intro M hM
  have hbool : spanContainsCodeCore [160, 68, 16, 8, 2, 1] (step99o377MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 256) ⊓ kerEvalFunc (codeMat 139 + codeMat 43)) ⊓ kerEvalFunc (codeMat 68)) at hM
    change ((evalFunc (codeMat 256) M = 0 ∧ evalFunc (codeMat 139 + codeMat 43) M = 0) ∧ evalFunc (codeMat 68) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [160, 68, 16, 8, 2, 1] (step99o377MatrixCodeNat M) hbool
  rwa [step99o377_codeMat_matrixCode] at hspan

private theorem step99o377s0_contain :
    step99o377ActualSource0 ≤ orbit29W := by
  apply step99o377_spanCodes_le_of_gens [160, 68, 16, 8, 2, 1] orbit29W
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 160 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 68 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 16 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 8 (by decide)
  · subst h4
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 2 (by decide)
  · subst h5
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 1 (by decide)

theorem step99o377s0Dispatch :
    QuotientRankAtLeast (o377SourceU ⟨0, by omega⟩) 15 :=
  quotientRankAtLeast_mono (le_trans step99o377s0_sourceU_le step99o377s0_contain) orbit29_lb15

-- Source 1 (row 25): orbit 231, lb 15
def step99o377ActualSource1 : Submodule F2 Mat3 := spanCodes [260, 161, 68, 19, 10]

private theorem step99o377s1_sourceU_le :
    (o377SourceU ⟨1, by omega⟩) ≤ step99o377ActualSource1 := by
  intro M hM
  have hbool : spanContainsCodeCore [260, 161, 68, 19, 10] (step99o377MatrixCodeNat M) = true := by
    change M ∈ (((kerEvalFunc (codeMat 256 + codeMat 68) ⊓ kerEvalFunc (codeMat 139)) ⊓ kerEvalFunc (codeMat 43)) ⊓ kerEvalFunc (codeMat 26)) at hM
    change (((evalFunc (codeMat 256 + codeMat 68) M = 0 ∧ evalFunc (codeMat 139) M = 0) ∧ evalFunc (codeMat 43) M = 0) ∧ evalFunc (codeMat 26) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 161, 68, 19, 10] (step99o377MatrixCodeNat M) hbool
  rwa [step99o377_codeMat_matrixCode] at hspan

private theorem step99o377s1_QtInv :
    (codeMat 339 : Mat3).transpose⁻¹ = (codeMat 467 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 339 : Mat3).transpose * (codeMat 467 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o377s1_targetSpan_le_action :
    step99o377ActualSource1 ≤ actionW (codeMat 372) (codeMat 339) o231W := by
  apply step99o377_spanCodes_le_of_gens [260, 161, 68, 19, 10]
    (actionW (codeMat 372) (codeMat 339) o231W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 256 ∈ o231W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 140, 98, 16, 1] 256 (by decide)
    have hact : actionA (codeMat 372) (codeMat 339) (codeMat 256) = codeMat 260 := by
      unfold actionA
      rw [step99o377s1_QtInv]
      show (codeMat 372 : Mat3).transpose * codeMat 256 * (codeMat 467 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 354 ∈ o231W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 140, 98, 16, 1] 354 (by decide)
    have hact : actionA (codeMat 372) (codeMat 339) (codeMat 354) = codeMat 161 := by
      unfold actionA
      rw [step99o377s1_QtInv]
      show (codeMat 372 : Mat3).transpose * codeMat 354 * (codeMat 467 : Mat3).transpose = codeMat 161
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 257 ∈ o231W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 140, 98, 16, 1] 257 (by decide)
    have hact : actionA (codeMat 372) (codeMat 339) (codeMat 257) = codeMat 68 := by
      unfold actionA
      rw [step99o377s1_QtInv]
      show (codeMat 372 : Mat3).transpose * codeMat 257 * (codeMat 467 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 413 ∈ o231W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 140, 98, 16, 1] 413 (by decide)
    have hact : actionA (codeMat 372) (codeMat 339) (codeMat 413) = codeMat 19 := by
      unfold actionA
      rw [step99o377s1_QtInv]
      show (codeMat 372 : Mat3).transpose * codeMat 413 * (codeMat 467 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 238 ∈ o231W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 140, 98, 16, 1] 238 (by decide)
    have hact : actionA (codeMat 372) (codeMat 339) (codeMat 238) = codeMat 10 := by
      unfold actionA
      rw [step99o377s1_QtInv]
      show (codeMat 372 : Mat3).transpose * codeMat 238 * (codeMat 467 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact

theorem step99o377s1Dispatch :
    QuotientRankAtLeast (o377SourceU ⟨1, by omega⟩) 15 := by
  have hP : Invertible (codeMat 372 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 339 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 372) (codeMat 339) o231W) 15 :=
    @quotientRankAtLeast_action (codeMat 372) (codeMat 339) hP hQ o231W 15 step99_orbit231_lb15_unconditional
  have hMono : QuotientRankAtLeast step99o377ActualSource1 15 :=
    quotientRankAtLeast_mono step99o377s1_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o377s1_sourceU_le hMono

-- Source 2 (row 26): orbit 67, lb 15
def step99o377ActualSource2 : Submodule F2 Mat3 := spanCodes [256, 161, 65, 19, 10, 5]

private theorem step99o377s2_sourceU_le :
    (o377SourceU ⟨2, by omega⟩) ≤ step99o377ActualSource2 := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 161, 65, 19, 10, 5] (step99o377MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 139 + codeMat 43) ⊓ kerEvalFunc (codeMat 68 + codeMat 43)) ⊓ kerEvalFunc (codeMat 26)) at hM
    change ((evalFunc (codeMat 139 + codeMat 43) M = 0 ∧ evalFunc (codeMat 68 + codeMat 43) M = 0) ∧ evalFunc (codeMat 26) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 161, 65, 19, 10, 5] (step99o377MatrixCodeNat M) hbool
  rwa [step99o377_codeMat_matrixCode] at hspan

private theorem step99o377s2_QtInv :
    (codeMat 157 : Mat3).transpose⁻¹ = (codeMat 486 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 157 : Mat3).transpose * (codeMat 486 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o377s2_targetSpan_le_action :
    step99o377ActualSource2 ≤ actionW (codeMat 140) (codeMat 157) o67W := by
  apply step99o377_spanCodes_le_of_gens [256, 161, 65, 19, 10, 5]
    (actionW (codeMat 140) (codeMat 157) o67W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 1 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 140) (codeMat 157) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step99o377s2_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 1 * (codeMat 486 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 94 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 94 (by decide)
    have hact : actionA (codeMat 140) (codeMat 157) (codeMat 94) = codeMat 161 := by
      unfold actionA
      rw [step99o377s2_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 94 * (codeMat 486 : Mat3).transpose = codeMat 161
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 27 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 27 (by decide)
    have hact : actionA (codeMat 140) (codeMat 157) (codeMat 27) = codeMat 65 := by
      unfold actionA
      rw [step99o377s2_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 27 * (codeMat 486 : Mat3).transpose = codeMat 65
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 424 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 424 (by decide)
    have hact : actionA (codeMat 140) (codeMat 157) (codeMat 424) = codeMat 19 := by
      unfold actionA
      rw [step99o377s2_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 424 * (codeMat 486 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 240 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 240 (by decide)
    have hact : actionA (codeMat 140) (codeMat 157) (codeMat 240) = codeMat 10 := by
      unfold actionA
      rw [step99o377s2_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 240 * (codeMat 486 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 140) (codeMat 157) (codeMat 16) = codeMat 5 := by
      unfold actionA
      rw [step99o377s2_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 16 * (codeMat 486 : Mat3).transpose = codeMat 5
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact

theorem step99o377s2Dispatch :
    QuotientRankAtLeast (o377SourceU ⟨2, by omega⟩) 15 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 157 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 157) o67W) 15 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 157) hP hQ o67W 15 step99_orbit67_lb15_unconditional
  have hMono : QuotientRankAtLeast step99o377ActualSource2 15 :=
    quotientRankAtLeast_mono step99o377s2_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o377s2_sourceU_le hMono

-- Source 3 (row 27): orbit 67, lb 15
def step99o377ActualSource3 : Submodule F2 Mat3 := spanCodes [257, 161, 64, 19, 10, 4]

private theorem step99o377s3_sourceU_le :
    (o377SourceU ⟨3, by omega⟩) ≤ step99o377ActualSource3 := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 161, 64, 19, 10, 4] (step99o377MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 256 + codeMat 43) ⊓ kerEvalFunc (codeMat 139 + codeMat 43)) ⊓ kerEvalFunc (codeMat 26)) at hM
    change ((evalFunc (codeMat 256 + codeMat 43) M = 0 ∧ evalFunc (codeMat 139 + codeMat 43) M = 0) ∧ evalFunc (codeMat 26) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 161, 64, 19, 10, 4] (step99o377MatrixCodeNat M) hbool
  rwa [step99o377_codeMat_matrixCode] at hspan

private theorem step99o377s3_QtInv :
    (codeMat 190 : Mat3).transpose⁻¹ = (codeMat 355 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 190 : Mat3).transpose * (codeMat 355 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o377s3_targetSpan_le_action :
    step99o377ActualSource3 ≤ actionW (codeMat 165) (codeMat 190) o67W := by
  apply step99o377_spanCodes_le_of_gens [257, 161, 64, 19, 10, 4]
    (actionW (codeMat 165) (codeMat 190) o67W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 10 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 165) (codeMat 190) (codeMat 10) = codeMat 257 := by
      unfold actionA
      rw [step99o377s3_QtInv]
      show (codeMat 165 : Mat3).transpose * codeMat 10 * (codeMat 355 : Mat3).transpose = codeMat 257
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 234 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 234 (by decide)
    have hact : actionA (codeMat 165) (codeMat 190) (codeMat 234) = codeMat 161 := by
      unfold actionA
      rw [step99o377s3_QtInv]
      show (codeMat 165 : Mat3).transpose * codeMat 234 * (codeMat 355 : Mat3).transpose = codeMat 161
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 16 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 165) (codeMat 190) (codeMat 16) = codeMat 64 := by
      unfold actionA
      rw [step99o377s3_QtInv]
      show (codeMat 165 : Mat3).transpose * codeMat 16 * (codeMat 355 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 493 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 493 (by decide)
    have hact : actionA (codeMat 165) (codeMat 190) (codeMat 493) = codeMat 19 := by
      unfold actionA
      rw [step99o377s3_QtInv]
      show (codeMat 165 : Mat3).transpose * codeMat 493 * (codeMat 355 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 191 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 191 (by decide)
    have hact : actionA (codeMat 165) (codeMat 190) (codeMat 191) = codeMat 10 := by
      unfold actionA
      rw [step99o377s3_QtInv]
      show (codeMat 165 : Mat3).transpose * codeMat 191 * (codeMat 355 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 27 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 27 (by decide)
    have hact : actionA (codeMat 165) (codeMat 190) (codeMat 27) = codeMat 4 := by
      unfold actionA
      rw [step99o377s3_QtInv]
      show (codeMat 165 : Mat3).transpose * codeMat 27 * (codeMat 355 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact

theorem step99o377s3Dispatch :
    QuotientRankAtLeast (o377SourceU ⟨3, by omega⟩) 15 := by
  have hP : Invertible (codeMat 165 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 190 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 165) (codeMat 190) o67W) 15 :=
    @quotientRankAtLeast_action (codeMat 165) (codeMat 190) hP hQ o67W 15 step99_orbit67_lb15_unconditional
  have hMono : QuotientRankAtLeast step99o377ActualSource3 15 :=
    quotientRankAtLeast_mono step99o377s3_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o377s3_sourceU_le hMono

-- Source 4 (row 28): orbit 67, lb 15
def step99o377ActualSource4 : Submodule F2 Mat3 := spanCodes [258, 161, 67, 19, 10, 7]

private theorem step99o377s4_sourceU_le :
    (o377SourceU ⟨4, by omega⟩) ≤ step99o377ActualSource4 := by
  intro M hM
  have hbool : spanContainsCodeCore [258, 161, 67, 19, 10, 7] (step99o377MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 256 + codeMat 43) ⊓ kerEvalFunc (codeMat 139 + codeMat 43)) ⊓ kerEvalFunc (codeMat 68 + codeMat 43 + codeMat 26)) at hM
    change ((evalFunc (codeMat 256 + codeMat 43) M = 0 ∧ evalFunc (codeMat 139 + codeMat 43) M = 0) ∧ evalFunc (codeMat 68 + codeMat 43 + codeMat 26) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 161, 67, 19, 10, 7] (step99o377MatrixCodeNat M) hbool
  rwa [step99o377_codeMat_matrixCode] at hspan

private theorem step99o377s4_QtInv :
    (codeMat 443 : Mat3).transpose⁻¹ = (codeMat 254 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 443 : Mat3).transpose * (codeMat 254 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o377s4_targetSpan_le_action :
    step99o377ActualSource4 ≤ actionW (codeMat 270) (codeMat 443) o67W := by
  apply step99o377_spanCodes_le_of_gens [258, 161, 67, 19, 10, 7]
    (actionW (codeMat 270) (codeMat 443) o67W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 440 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 440 (by decide)
    have hact : actionA (codeMat 270) (codeMat 443) (codeMat 440) = codeMat 258 := by
      unfold actionA
      rw [step99o377s4_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 440 * (codeMat 254 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 94 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 94 (by decide)
    have hact : actionA (codeMat 270) (codeMat 443) (codeMat 94) = codeMat 161 := by
      unfold actionA
      rw [step99o377s4_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 94 * (codeMat 254 : Mat3).transpose = codeMat 161
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 224 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 224 (by decide)
    have hact : actionA (codeMat 270) (codeMat 443) (codeMat 224) = codeMat 67 := by
      unfold actionA
      rw [step99o377s4_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 224 * (codeMat 254 : Mat3).transpose = codeMat 67
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 487 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 487 (by decide)
    have hact : actionA (codeMat 270) (codeMat 443) (codeMat 487) = codeMat 19 := by
      unfold actionA
      rw [step99o377s4_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 487 * (codeMat 254 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 251 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 251 (by decide)
    have hact : actionA (codeMat 270) (codeMat 443) (codeMat 251) = codeMat 10 := by
      unfold actionA
      rw [step99o377s4_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 251 * (codeMat 254 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 270) (codeMat 443) (codeMat 16) = codeMat 7 := by
      unfold actionA
      rw [step99o377s4_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 16 * (codeMat 254 : Mat3).transpose = codeMat 7
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact

theorem step99o377s4Dispatch :
    QuotientRankAtLeast (o377SourceU ⟨4, by omega⟩) 15 := by
  have hP : Invertible (codeMat 270 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 443 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 270) (codeMat 443) o67W) 15 :=
    @quotientRankAtLeast_action (codeMat 270) (codeMat 443) hP hQ o67W 15 step99_orbit67_lb15_unconditional
  have hMono : QuotientRankAtLeast step99o377ActualSource4 15 :=
    quotientRankAtLeast_mono step99o377s4_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o377s4_sourceU_le hMono

-- Source 5 (row 29): orbit 67, lb 15
def step99o377ActualSource5 : Submodule F2 Mat3 := spanCodes [259, 161, 66, 19, 10, 6]

private theorem step99o377s5_sourceU_le :
    (o377SourceU ⟨5, by omega⟩) ≤ step99o377ActualSource5 := by
  intro M hM
  have hbool : spanContainsCodeCore [259, 161, 66, 19, 10, 6] (step99o377MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 256 + codeMat 43 + codeMat 26) ⊓ kerEvalFunc (codeMat 139 + codeMat 43)) ⊓ kerEvalFunc (codeMat 68 + codeMat 43)) at hM
    change ((evalFunc (codeMat 256 + codeMat 43 + codeMat 26) M = 0 ∧ evalFunc (codeMat 139 + codeMat 43) M = 0) ∧ evalFunc (codeMat 68 + codeMat 43) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [259, 161, 66, 19, 10, 6] (step99o377MatrixCodeNat M) hbool
  rwa [step99o377_codeMat_matrixCode] at hspan

private theorem step99o377s5_QtInv :
    (codeMat 428 : Mat3).transpose⁻¹ = (codeMat 107 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 428 : Mat3).transpose * (codeMat 107 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o377s5_targetSpan_le_action :
    step99o377ActualSource5 ≤ actionW (codeMat 311) (codeMat 428) o67W := by
  apply step99o377_spanCodes_le_of_gens [259, 161, 66, 19, 10, 6]
    (actionW (codeMat 311) (codeMat 428) o67W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 502 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 502 (by decide)
    have hact : actionA (codeMat 311) (codeMat 428) (codeMat 502) = codeMat 259 := by
      unfold actionA
      rw [step99o377s5_QtInv]
      show (codeMat 311 : Mat3).transpose * codeMat 502 * (codeMat 107 : Mat3).transpose = codeMat 259
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 234 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 234 (by decide)
    have hact : actionA (codeMat 311) (codeMat 428) (codeMat 234) = codeMat 161 := by
      unfold actionA
      rw [step99o377s5_QtInv]
      show (codeMat 311 : Mat3).transpose * codeMat 234 * (codeMat 107 : Mat3).transpose = codeMat 161
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 164 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 164 (by decide)
    have hact : actionA (codeMat 311) (codeMat 428) (codeMat 164) = codeMat 66 := by
      unfold actionA
      rw [step99o377s5_QtInv]
      show (codeMat 311 : Mat3).transpose * codeMat 164 * (codeMat 107 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 278 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 278 (by decide)
    have hact : actionA (codeMat 311) (codeMat 428) (codeMat 278) = codeMat 19 := by
      unfold actionA
      rw [step99o377s5_QtInv]
      show (codeMat 311 : Mat3).transpose * codeMat 278 * (codeMat 107 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 180 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 180 (by decide)
    have hact : actionA (codeMat 311) (codeMat 428) (codeMat 180) = codeMat 10 := by
      unfold actionA
      rw [step99o377s5_QtInv]
      show (codeMat 311 : Mat3).transpose * codeMat 180 * (codeMat 107 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 27 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 27 (by decide)
    have hact : actionA (codeMat 311) (codeMat 428) (codeMat 27) = codeMat 6 := by
      unfold actionA
      rw [step99o377s5_QtInv]
      show (codeMat 311 : Mat3).transpose * codeMat 27 * (codeMat 107 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact

theorem step99o377s5Dispatch :
    QuotientRankAtLeast (o377SourceU ⟨5, by omega⟩) 15 := by
  have hP : Invertible (codeMat 311 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 428 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 311) (codeMat 428) o67W) 15 :=
    @quotientRankAtLeast_action (codeMat 311) (codeMat 428) hP hQ o67W 15 step99_orbit67_lb15_unconditional
  have hMono : QuotientRankAtLeast step99o377ActualSource5 15 :=
    quotientRankAtLeast_mono step99o377s5_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o377s5_sourceU_le hMono

-- Source 6 (row 34): orbit 67, lb 15
def step99o377ActualSource6 : Submodule F2 Mat3 := spanCodes [262, 135, 68, 38, 19, 10]

private theorem step99o377s6_sourceU_le :
    (o377SourceU ⟨6, by omega⟩) ≤ step99o377ActualSource6 := by
  intro M hM
  have hbool : spanContainsCodeCore [262, 135, 68, 38, 19, 10] (step99o377MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 256 + codeMat 43) ⊓ kerEvalFunc (codeMat 139 + codeMat 26)) ⊓ kerEvalFunc (codeMat 68 + codeMat 26)) at hM
    change ((evalFunc (codeMat 256 + codeMat 43) M = 0 ∧ evalFunc (codeMat 139 + codeMat 26) M = 0) ∧ evalFunc (codeMat 68 + codeMat 26) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 135, 68, 38, 19, 10] (step99o377MatrixCodeNat M) hbool
  rwa [step99o377_codeMat_matrixCode] at hspan

private theorem step99o377s6_QtInv :
    (codeMat 212 : Mat3).transpose⁻¹ = (codeMat 86 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 212 : Mat3).transpose * (codeMat 86 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o377s6_targetSpan_le_action :
    step99o377ActualSource6 ≤ actionW (codeMat 302) (codeMat 212) o67W := by
  apply step99o377_spanCodes_le_of_gens [262, 135, 68, 38, 19, 10]
    (actionW (codeMat 302) (codeMat 212) o67W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 440 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 440 (by decide)
    have hact : actionA (codeMat 302) (codeMat 212) (codeMat 440) = codeMat 262 := by
      unfold actionA
      rw [step99o377s6_QtInv]
      show (codeMat 302 : Mat3).transpose * codeMat 440 * (codeMat 86 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 344 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 344 (by decide)
    have hact : actionA (codeMat 302) (codeMat 212) (codeMat 344) = codeMat 135 := by
      unfold actionA
      rw [step99o377s6_QtInv]
      show (codeMat 302 : Mat3).transpose * codeMat 344 * (codeMat 86 : Mat3).transpose = codeMat 135
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 328 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 328 (by decide)
    have hact : actionA (codeMat 302) (codeMat 212) (codeMat 328) = codeMat 68 := by
      unfold actionA
      rw [step99o377s6_QtInv]
      show (codeMat 302 : Mat3).transpose * codeMat 328 * (codeMat 86 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 441 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 441 (by decide)
    have hact : actionA (codeMat 302) (codeMat 212) (codeMat 441) = codeMat 38 := by
      unfold actionA
      rw [step99o377s6_QtInv]
      show (codeMat 302 : Mat3).transpose * codeMat 441 * (codeMat 86 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 278 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 278 (by decide)
    have hact : actionA (codeMat 302) (codeMat 212) (codeMat 278) = codeMat 19 := by
      unfold actionA
      rw [step99o377s6_QtInv]
      show (codeMat 302 : Mat3).transpose * codeMat 278 * (codeMat 86 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 180 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 180 (by decide)
    have hact : actionA (codeMat 302) (codeMat 212) (codeMat 180) = codeMat 10 := by
      unfold actionA
      rw [step99o377s6_QtInv]
      show (codeMat 302 : Mat3).transpose * codeMat 180 * (codeMat 86 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact

theorem step99o377s6Dispatch :
    QuotientRankAtLeast (o377SourceU ⟨6, by omega⟩) 15 := by
  have hP : Invertible (codeMat 302 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 212 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 302) (codeMat 212) o67W) 15 :=
    @quotientRankAtLeast_action (codeMat 302) (codeMat 212) hP hQ o67W 15 step99_orbit67_lb15_unconditional
  have hMono : QuotientRankAtLeast step99o377ActualSource6 15 :=
    quotientRankAtLeast_mono step99o377s6_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o377s6_sourceU_le hMono

-- Source 7 (row 36): orbit 67, lb 15
def step99o377ActualSource7 : Submodule F2 Mat3 := spanCodes [262, 134, 68, 39, 19, 10]

private theorem step99o377s7_sourceU_le :
    (o377SourceU ⟨7, by omega⟩) ≤ step99o377ActualSource7 := by
  intro M hM
  have hbool : spanContainsCodeCore [262, 134, 68, 39, 19, 10] (step99o377MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 256 + codeMat 139) ⊓ kerEvalFunc (codeMat 68 + codeMat 26)) ⊓ kerEvalFunc (codeMat 43 + codeMat 26)) at hM
    change ((evalFunc (codeMat 256 + codeMat 139) M = 0 ∧ evalFunc (codeMat 68 + codeMat 26) M = 0) ∧ evalFunc (codeMat 43 + codeMat 26) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 134, 68, 39, 19, 10] (step99o377MatrixCodeNat M) hbool
  rwa [step99o377_codeMat_matrixCode] at hspan

private theorem step99o377s7_QtInv :
    (codeMat 501 : Mat3).transpose⁻¹ = (codeMat 494 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 501 : Mat3).transpose * (codeMat 494 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o377s7_targetSpan_le_action :
    step99o377ActualSource7 ≤ actionW (codeMat 156) (codeMat 501) o67W := by
  apply step99o377_spanCodes_le_of_gens [262, 134, 68, 39, 19, 10]
    (actionW (codeMat 156) (codeMat 501) o67W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 79 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 79 (by decide)
    have hact : actionA (codeMat 156) (codeMat 501) (codeMat 79) = codeMat 262 := by
      unfold actionA
      rw [step99o377s7_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 79 * (codeMat 494 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 78 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 78 (by decide)
    have hact : actionA (codeMat 156) (codeMat 501) (codeMat 78) = codeMat 134 := by
      unfold actionA
      rw [step99o377s7_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 78 * (codeMat 494 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 509 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 509 (by decide)
    have hact : actionA (codeMat 156) (codeMat 501) (codeMat 509) = codeMat 68 := by
      unfold actionA
      rw [step99o377s7_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 509 * (codeMat 494 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 224 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 224 (by decide)
    have hact : actionA (codeMat 156) (codeMat 501) (codeMat 224) = codeMat 39 := by
      unfold actionA
      rw [step99o377s7_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 224 * (codeMat 494 : Mat3).transpose = codeMat 39
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 344 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 344 (by decide)
    have hact : actionA (codeMat 156) (codeMat 501) (codeMat 344) = codeMat 19 := by
      unfold actionA
      rw [step99o377s7_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 344 * (codeMat 494 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 240 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 240 (by decide)
    have hact : actionA (codeMat 156) (codeMat 501) (codeMat 240) = codeMat 10 := by
      unfold actionA
      rw [step99o377s7_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 240 * (codeMat 494 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact

theorem step99o377s7Dispatch :
    QuotientRankAtLeast (o377SourceU ⟨7, by omega⟩) 15 := by
  have hP : Invertible (codeMat 156 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 501 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 156) (codeMat 501) o67W) 15 :=
    @quotientRankAtLeast_action (codeMat 156) (codeMat 501) hP hQ o67W 15 step99_orbit67_lb15_unconditional
  have hMono : QuotientRankAtLeast step99o377ActualSource7 15 :=
    quotientRankAtLeast_mono step99o377s7_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o377s7_sourceU_le hMono

-- Source 8 (row 38): orbit 67, lb 15
def step99o377ActualSource8 : Submodule F2 Mat3 := spanCodes [262, 133, 68, 36, 19, 10]

private theorem step99o377s8_sourceU_le :
    (o377SourceU ⟨8, by omega⟩) ≤ step99o377ActualSource8 := by
  intro M hM
  have hbool : spanContainsCodeCore [262, 133, 68, 36, 19, 10] (step99o377MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 256 + codeMat 26) ⊓ kerEvalFunc (codeMat 139 + codeMat 26)) ⊓ kerEvalFunc (codeMat 68 + codeMat 43)) at hM
    change ((evalFunc (codeMat 256 + codeMat 26) M = 0 ∧ evalFunc (codeMat 139 + codeMat 26) M = 0) ∧ evalFunc (codeMat 68 + codeMat 43) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 133, 68, 36, 19, 10] (step99o377MatrixCodeNat M) hbool
  rwa [step99o377_codeMat_matrixCode] at hspan

private theorem step99o377s8_QtInv :
    (codeMat 236 : Mat3).transpose⁻¹ = (codeMat 123 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 236 : Mat3).transpose * (codeMat 123 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o377s8_targetSpan_le_action :
    step99o377ActualSource8 ≤ actionW (codeMat 309) (codeMat 236) o67W := by
  apply step99o377_spanCodes_le_of_gens [262, 133, 68, 36, 19, 10]
    (actionW (codeMat 309) (codeMat 236) o67W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 263 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 263 (by decide)
    have hact : actionA (codeMat 309) (codeMat 236) (codeMat 263) = codeMat 262 := by
      unfold actionA
      rw [step99o377s8_QtInv]
      show (codeMat 309 : Mat3).transpose * codeMat 263 * (codeMat 123 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 69 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 69 (by decide)
    have hact : actionA (codeMat 309) (codeMat 236) (codeMat 69) = codeMat 133 := by
      unfold actionA
      rw [step99o377s8_QtInv]
      show (codeMat 309 : Mat3).transpose * codeMat 69 * (codeMat 123 : Mat3).transpose = codeMat 133
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 323 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 323 (by decide)
    have hact : actionA (codeMat 309) (codeMat 236) (codeMat 323) = codeMat 68 := by
      unfold actionA
      rw [step99o377s8_QtInv]
      show (codeMat 309 : Mat3).transpose * codeMat 323 * (codeMat 123 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 27 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 27 (by decide)
    have hact : actionA (codeMat 309) (codeMat 236) (codeMat 27) = codeMat 36 := by
      unfold actionA
      rw [step99o377s8_QtInv]
      show (codeMat 309 : Mat3).transpose * codeMat 27 * (codeMat 123 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 418 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 418 (by decide)
    have hact : actionA (codeMat 309) (codeMat 236) (codeMat 418) = codeMat 19 := by
      unfold actionA
      rw [step99o377s8_QtInv]
      show (codeMat 309 : Mat3).transpose * codeMat 418 * (codeMat 123 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 180 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 180 (by decide)
    have hact : actionA (codeMat 309) (codeMat 236) (codeMat 180) = codeMat 10 := by
      unfold actionA
      rw [step99o377s8_QtInv]
      show (codeMat 309 : Mat3).transpose * codeMat 180 * (codeMat 123 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact

theorem step99o377s8Dispatch :
    QuotientRankAtLeast (o377SourceU ⟨8, by omega⟩) 15 := by
  have hP : Invertible (codeMat 309 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 236 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 309) (codeMat 236) o67W) 15 :=
    @quotientRankAtLeast_action (codeMat 309) (codeMat 236) hP hQ o67W 15 step99_orbit67_lb15_unconditional
  have hMono : QuotientRankAtLeast step99o377ActualSource8 15 :=
    quotientRankAtLeast_mono step99o377s8_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o377s8_sourceU_le hMono

-- Source 9 (row 41): orbit 67, lb 15
def step99o377ActualSource9 : Submodule F2 Mat3 := spanCodes [262, 132, 68, 37, 19, 10]

private theorem step99o377s9_sourceU_le :
    (o377SourceU ⟨9, by omega⟩) ≤ step99o377ActualSource9 := by
  intro M hM
  have hbool : spanContainsCodeCore [262, 132, 68, 37, 19, 10] (step99o377MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 256 + codeMat 26) ⊓ kerEvalFunc (codeMat 139 + codeMat 68)) ⊓ kerEvalFunc (codeMat 43 + codeMat 26)) at hM
    change ((evalFunc (codeMat 256 + codeMat 26) M = 0 ∧ evalFunc (codeMat 139 + codeMat 68) M = 0) ∧ evalFunc (codeMat 43 + codeMat 26) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 132, 68, 37, 19, 10] (step99o377MatrixCodeNat M) hbool
  rwa [step99o377_codeMat_matrixCode] at hspan

private theorem step99o377s9_QtInv :
    (codeMat 467 : Mat3).transpose⁻¹ = (codeMat 339 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 467 : Mat3).transpose * (codeMat 339 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o377s9_targetSpan_le_action :
    step99o377ActualSource9 ≤ actionW (codeMat 167) (codeMat 467) o67W := by
  apply step99o377_spanCodes_le_of_gens [262, 132, 68, 37, 19, 10]
    (actionW (codeMat 167) (codeMat 467) o67W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 251 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 251 (by decide)
    have hact : actionA (codeMat 167) (codeMat 467) (codeMat 251) = codeMat 262 := by
      unfold actionA
      rw [step99o377s9_QtInv]
      show (codeMat 167 : Mat3).transpose * codeMat 251 * (codeMat 339 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 284 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 284 (by decide)
    have hact : actionA (codeMat 167) (codeMat 467) (codeMat 284) = codeMat 132 := by
      unfold actionA
      rw [step99o377s9_QtInv]
      show (codeMat 167 : Mat3).transpose * codeMat 284 * (codeMat 339 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 268 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 268 (by decide)
    have hact : actionA (codeMat 167) (codeMat 467) (codeMat 268) = codeMat 68 := by
      unfold actionA
      rw [step99o377s9_QtInv]
      show (codeMat 167 : Mat3).transpose * codeMat 268 * (codeMat 339 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 329 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 329 (by decide)
    have hact : actionA (codeMat 167) (codeMat 467) (codeMat 329) = codeMat 37 := by
      unfold actionA
      rw [step99o377s9_QtInv]
      show (codeMat 167 : Mat3).transpose * codeMat 329 * (codeMat 339 : Mat3).transpose = codeMat 37
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 338 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 338 (by decide)
    have hact : actionA (codeMat 167) (codeMat 467) (codeMat 338) = codeMat 19 := by
      unfold actionA
      rw [step99o377s9_QtInv]
      show (codeMat 167 : Mat3).transpose * codeMat 338 * (codeMat 339 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 191 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 191 (by decide)
    have hact : actionA (codeMat 167) (codeMat 467) (codeMat 191) = codeMat 10 := by
      unfold actionA
      rw [step99o377s9_QtInv]
      show (codeMat 167 : Mat3).transpose * codeMat 191 * (codeMat 339 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact

theorem step99o377s9Dispatch :
    QuotientRankAtLeast (o377SourceU ⟨9, by omega⟩) 15 := by
  have hP : Invertible (codeMat 167 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 467 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 167) (codeMat 467) o67W) 15 :=
    @quotientRankAtLeast_action (codeMat 167) (codeMat 467) hP hQ o67W 15 step99_orbit67_lb15_unconditional
  have hMono : QuotientRankAtLeast step99o377ActualSource9 15 :=
    quotientRankAtLeast_mono step99o377s9_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o377s9_sourceU_le hMono

-- Source 10 (row 44): orbit 67, lb 15
def step99o377ActualSource10 : Submodule F2 Mat3 := spanCodes [263, 130, 68, 35, 19, 10]

private theorem step99o377s10_sourceU_le :
    (o377SourceU ⟨10, by omega⟩) ≤ step99o377ActualSource10 := by
  intro M hM
  have hbool : spanContainsCodeCore [263, 130, 68, 35, 19, 10] (step99o377MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 256 + codeMat 43 + codeMat 26) ⊓ kerEvalFunc (codeMat 139)) ⊓ kerEvalFunc (codeMat 68 + codeMat 43 + codeMat 26)) at hM
    change ((evalFunc (codeMat 256 + codeMat 43 + codeMat 26) M = 0 ∧ evalFunc (codeMat 139) M = 0) ∧ evalFunc (codeMat 68 + codeMat 43 + codeMat 26) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [263, 130, 68, 35, 19, 10] (step99o377MatrixCodeNat M) hbool
  rwa [step99o377_codeMat_matrixCode] at hspan

private theorem step99o377s10_QtInv :
    (codeMat 86 : Mat3).transpose⁻¹ = (codeMat 212 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 86 : Mat3).transpose * (codeMat 212 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o377s10_targetSpan_le_action :
    step99o377ActualSource10 ≤ actionW (codeMat 279) (codeMat 86) o67W := by
  apply step99o377_spanCodes_le_of_gens [263, 130, 68, 35, 19, 10]
    (actionW (codeMat 279) (codeMat 86) o67W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 502 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 502 (by decide)
    have hact : actionA (codeMat 279) (codeMat 86) (codeMat 502) = codeMat 263 := by
      unfold actionA
      rw [step99o377s10_QtInv]
      show (codeMat 279 : Mat3).transpose * codeMat 502 * (codeMat 212 : Mat3).transpose = codeMat 263
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 27 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 27 (by decide)
    have hact : actionA (codeMat 279) (codeMat 86) (codeMat 27) = codeMat 130 := by
      unfold actionA
      rw [step99o377s10_QtInv]
      show (codeMat 279 : Mat3).transpose * codeMat 27 * (codeMat 212 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 329 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 329 (by decide)
    have hact : actionA (codeMat 279) (codeMat 86) (codeMat 329) = codeMat 68 := by
      unfold actionA
      rw [step99o377s10_QtInv]
      show (codeMat 279 : Mat3).transpose * codeMat 329 * (codeMat 212 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 503 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 503 (by decide)
    have hact : actionA (codeMat 279) (codeMat 86) (codeMat 503) = codeMat 35 := by
      unfold actionA
      rw [step99o377s10_QtInv]
      show (codeMat 279 : Mat3).transpose * codeMat 503 * (codeMat 212 : Mat3).transpose = codeMat 35
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 487 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 487 (by decide)
    have hact : actionA (codeMat 279) (codeMat 86) (codeMat 487) = codeMat 19 := by
      unfold actionA
      rw [step99o377s10_QtInv]
      show (codeMat 279 : Mat3).transpose * codeMat 487 * (codeMat 212 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 251 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 251 (by decide)
    have hact : actionA (codeMat 279) (codeMat 86) (codeMat 251) = codeMat 10 := by
      unfold actionA
      rw [step99o377s10_QtInv]
      show (codeMat 279 : Mat3).transpose * codeMat 251 * (codeMat 212 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact

theorem step99o377s10Dispatch :
    QuotientRankAtLeast (o377SourceU ⟨10, by omega⟩) 15 := by
  have hP : Invertible (codeMat 279 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 86 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 279) (codeMat 86) o67W) 15 :=
    @quotientRankAtLeast_action (codeMat 279) (codeMat 86) hP hQ o67W 15 step99_orbit67_lb15_unconditional
  have hMono : QuotientRankAtLeast step99o377ActualSource10 15 :=
    quotientRankAtLeast_mono step99o377s10_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o377s10_sourceU_le hMono

-- Source 11 (row 46): orbit 67, lb 15
def step99o377ActualSource11 : Submodule F2 Mat3 := spanCodes [263, 131, 68, 34, 19, 10]

private theorem step99o377s11_sourceU_le :
    (o377SourceU ⟨11, by omega⟩) ≤ step99o377ActualSource11 := by
  intro M hM
  have hbool : spanContainsCodeCore [263, 131, 68, 34, 19, 10] (step99o377MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 256 + codeMat 68) ⊓ kerEvalFunc (codeMat 139 + codeMat 68 + codeMat 26)) ⊓ kerEvalFunc (codeMat 43)) at hM
    change ((evalFunc (codeMat 256 + codeMat 68) M = 0 ∧ evalFunc (codeMat 139 + codeMat 68 + codeMat 26) M = 0) ∧ evalFunc (codeMat 43) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [263, 131, 68, 34, 19, 10] (step99o377MatrixCodeNat M) hbool
  rwa [step99o377_codeMat_matrixCode] at hspan

private theorem step99o377s11_QtInv :
    (codeMat 346 : Mat3).transpose⁻¹ = (codeMat 459 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 346 : Mat3).transpose * (codeMat 459 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o377s11_targetSpan_le_action :
    step99o377ActualSource11 ≤ actionW (codeMat 84) (codeMat 346) o67W := by
  apply step99o377_spanCodes_le_of_gens [263, 131, 68, 34, 19, 10]
    (actionW (codeMat 84) (codeMat 346) o67W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 68 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 84) (codeMat 346) (codeMat 68) = codeMat 263 := by
      unfold actionA
      rw [step99o377s11_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 68 * (codeMat 459 : Mat3).transpose = codeMat 263
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 323 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 323 (by decide)
    have hact : actionA (codeMat 84) (codeMat 346) (codeMat 323) = codeMat 131 := by
      unfold actionA
      rw [step99o377s11_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 323 * (codeMat 459 : Mat3).transpose = codeMat 131
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 262 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 262 (by decide)
    have hact : actionA (codeMat 84) (codeMat 346) (codeMat 262) = codeMat 68 := by
      unfold actionA
      rw [step99o377s11_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 262 * (codeMat 459 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 224 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 224 (by decide)
    have hact : actionA (codeMat 84) (codeMat 346) (codeMat 224) = codeMat 34 := by
      unfold actionA
      rw [step99o377s11_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 224 * (codeMat 459 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 344 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 344 (by decide)
    have hact : actionA (codeMat 84) (codeMat 346) (codeMat 344) = codeMat 19 := by
      unfold actionA
      rw [step99o377s11_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 344 * (codeMat 459 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 240 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 240 (by decide)
    have hact : actionA (codeMat 84) (codeMat 346) (codeMat 240) = codeMat 10 := by
      unfold actionA
      rw [step99o377s11_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 240 * (codeMat 459 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact

theorem step99o377s11Dispatch :
    QuotientRankAtLeast (o377SourceU ⟨11, by omega⟩) 15 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 346 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 346) o67W) 15 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 346) hP hQ o67W 15 step99_orbit67_lb15_unconditional
  have hMono : QuotientRankAtLeast step99o377ActualSource11 15 :=
    quotientRankAtLeast_mono step99o377s11_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o377s11_sourceU_le hMono

-- Source 12 (row 48): orbit 67, lb 15
def step99o377ActualSource12 : Submodule F2 Mat3 := spanCodes [263, 128, 68, 33, 19, 10]

private theorem step99o377s12_sourceU_le :
    (o377SourceU ⟨12, by omega⟩) ≤ step99o377ActualSource12 := by
  intro M hM
  have hbool : spanContainsCodeCore [263, 128, 68, 33, 19, 10] (step99o377MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 256 + codeMat 26) ⊓ kerEvalFunc (codeMat 68 + codeMat 26)) ⊓ kerEvalFunc (codeMat 43)) at hM
    change ((evalFunc (codeMat 256 + codeMat 26) M = 0 ∧ evalFunc (codeMat 68 + codeMat 26) M = 0) ∧ evalFunc (codeMat 43) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [263, 128, 68, 33, 19, 10] (step99o377MatrixCodeNat M) hbool
  rwa [step99o377_codeMat_matrixCode] at hspan

private theorem step99o377s12_QtInv :
    (codeMat 377 : Mat3).transpose⁻¹ = (codeMat 369 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 377 : Mat3).transpose * (codeMat 369 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o377s12_targetSpan_le_action :
    step99o377ActualSource12 ≤ actionW (codeMat 102) (codeMat 377) o67W := by
  apply step99o377_spanCodes_le_of_gens [263, 128, 68, 33, 19, 10]
    (actionW (codeMat 102) (codeMat 377) o67W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 240 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 240 (by decide)
    have hact : actionA (codeMat 102) (codeMat 377) (codeMat 240) = codeMat 263 := by
      unfold actionA
      rw [step99o377s12_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 240 * (codeMat 369 : Mat3).transpose = codeMat 263
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 16 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 102) (codeMat 377) (codeMat 16) = codeMat 128 := by
      unfold actionA
      rw [step99o377s12_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 16 * (codeMat 369 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 440 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 440 (by decide)
    have hact : actionA (codeMat 102) (codeMat 377) (codeMat 440) = codeMat 68 := by
      unfold actionA
      rw [step99o377s12_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 440 * (codeMat 369 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 502 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 502 (by decide)
    have hact : actionA (codeMat 102) (codeMat 377) (codeMat 502) = codeMat 33 := by
      unfold actionA
      rw [step99o377s12_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 502 * (codeMat 369 : Mat3).transpose = codeMat 33
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 338 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 338 (by decide)
    have hact : actionA (codeMat 102) (codeMat 377) (codeMat 338) = codeMat 19 := by
      unfold actionA
      rw [step99o377s12_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 338 * (codeMat 369 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 191 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 191 (by decide)
    have hact : actionA (codeMat 102) (codeMat 377) (codeMat 191) = codeMat 10 := by
      unfold actionA
      rw [step99o377s12_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 191 * (codeMat 369 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact

theorem step99o377s12Dispatch :
    QuotientRankAtLeast (o377SourceU ⟨12, by omega⟩) 15 := by
  have hP : Invertible (codeMat 102 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 377 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 102) (codeMat 377) o67W) 15 :=
    @quotientRankAtLeast_action (codeMat 102) (codeMat 377) hP hQ o67W 15 step99_orbit67_lb15_unconditional
  have hMono : QuotientRankAtLeast step99o377ActualSource12 15 :=
    quotientRankAtLeast_mono step99o377s12_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o377s12_sourceU_le hMono

-- Source 13 (row 51): orbit 67, lb 15
def step99o377ActualSource13 : Submodule F2 Mat3 := spanCodes [263, 129, 68, 32, 19, 10]

private theorem step99o377s13_sourceU_le :
    (o377SourceU ⟨13, by omega⟩) ≤ step99o377ActualSource13 := by
  intro M hM
  have hbool : spanContainsCodeCore [263, 129, 68, 32, 19, 10] (step99o377MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 256 + codeMat 26) ⊓ kerEvalFunc (codeMat 139)) ⊓ kerEvalFunc (codeMat 68 + codeMat 26)) at hM
    change ((evalFunc (codeMat 256 + codeMat 26) M = 0 ∧ evalFunc (codeMat 139) M = 0) ∧ evalFunc (codeMat 68 + codeMat 26) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [263, 129, 68, 32, 19, 10] (step99o377MatrixCodeNat M) hbool
  rwa [step99o377_codeMat_matrixCode] at hspan

private theorem step99o377s13_QtInv :
    (codeMat 123 : Mat3).transpose⁻¹ = (codeMat 236 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 123 : Mat3).transpose * (codeMat 236 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o377s13_targetSpan_le_action :
    step99o377ActualSource13 ≤ actionW (codeMat 277) (codeMat 123) o67W := by
  apply step99o377_spanCodes_le_of_gens [263, 129, 68, 32, 19, 10]
    (actionW (codeMat 277) (codeMat 123) o67W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 262 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 262 (by decide)
    have hact : actionA (codeMat 277) (codeMat 123) (codeMat 262) = codeMat 263 := by
      unfold actionA
      rw [step99o377s13_QtInv]
      show (codeMat 277 : Mat3).transpose * codeMat 262 * (codeMat 236 : Mat3).transpose = codeMat 263
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 263 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 263 (by decide)
    have hact : actionA (codeMat 277) (codeMat 123) (codeMat 263) = codeMat 129 := by
      unfold actionA
      rw [step99o377s13_QtInv]
      show (codeMat 277 : Mat3).transpose * codeMat 263 * (codeMat 236 : Mat3).transpose = codeMat 129
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 322 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 322 (by decide)
    have hact : actionA (codeMat 277) (codeMat 123) (codeMat 322) = codeMat 68 := by
      unfold actionA
      rw [step99o377s13_QtInv]
      show (codeMat 277 : Mat3).transpose * codeMat 322 * (codeMat 236 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 16 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 277) (codeMat 123) (codeMat 16) = codeMat 32 := by
      unfold actionA
      rw [step99o377s13_QtInv]
      show (codeMat 277 : Mat3).transpose * codeMat 16 * (codeMat 236 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 284 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 284 (by decide)
    have hact : actionA (codeMat 277) (codeMat 123) (codeMat 284) = codeMat 19 := by
      unfold actionA
      rw [step99o377s13_QtInv]
      show (codeMat 277 : Mat3).transpose * codeMat 284 * (codeMat 236 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 251 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 251 (by decide)
    have hact : actionA (codeMat 277) (codeMat 123) (codeMat 251) = codeMat 10 := by
      unfold actionA
      rw [step99o377s13_QtInv]
      show (codeMat 277 : Mat3).transpose * codeMat 251 * (codeMat 236 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o377_codeMat_mem_actionW_of_witness hw hact

theorem step99o377s13Dispatch :
    QuotientRankAtLeast (o377SourceU ⟨13, by omega⟩) 15 := by
  have hP : Invertible (codeMat 277 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 123 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 277) (codeMat 123) o67W) 15 :=
    @quotientRankAtLeast_action (codeMat 277) (codeMat 123) hP hQ o67W 15 step99_orbit67_lb15_unconditional
  have hMono : QuotientRankAtLeast step99o377ActualSource13 15 :=
    quotientRankAtLeast_mono step99o377s13_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o377s13_sourceU_le hMono

theorem step99o377_all_dispatch (i : Fin 14) :
    QuotientRankAtLeast (o377SourceU i) (o377SourceLb i) := by
  fin_cases i
  · exact step99o377s0Dispatch
  · exact step99o377s1Dispatch
  · exact step99o377s2Dispatch
  · exact step99o377s3Dispatch
  · exact step99o377s4Dispatch
  · exact step99o377s5Dispatch
  · exact step99o377s6Dispatch
  · exact step99o377s7Dispatch
  · exact step99o377s8Dispatch
  · exact step99o377s9Dispatch
  · exact step99o377s10Dispatch
  · exact step99o377s11Dispatch
  · exact step99o377s12Dispatch
  · exact step99o377s13Dispatch

theorem step99_orbit377_lb17_unconditional :
    QuotientRankAtLeast o377W 17 :=
  o377Lb17 step99o377_all_dispatch

end QiushiMatmul
