import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbit10FP
import QiushiOrbit5FP
import QiushiOrbitTransport
import QiushiStep98Orbit120Consumer
import QiushiStep99Mono3032
import QiushiStep99Orbit55Dispatch

set_option maxHeartbeats 800000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem step99o120_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step99o120MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step99o120_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step99o120MatrixCodeNat M) = M := by decide

lemma step99o120_codeMat_matrixCode (M : Mat3) :
    codeMat (step99o120MatrixCodeNat M) = M :=
  step99o120_codeMat_matrixCode_all M

private theorem step99o120_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step99o120_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

-- Source 0 (row 0): orbit 55, lb 14
def step99o120ActualSource0 : Submodule F2 Mat3 := spanCodes [272, 132, 32, 12, 2, 1]

private theorem step99o120s0_sourceU_le :
    (o120SourceU ⟨0, by omega⟩) ≤ step99o120ActualSource0 := by
  intro M hM
  have hbool : spanContainsCodeCore [272, 132, 32, 12, 2, 1] (step99o120MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 272) ⊓ kerEvalFunc (codeMat 128 + codeMat 12)) ⊓ kerEvalFunc (codeMat 64)) at hM
    change ((evalFunc (codeMat 272) M = 0 ∧ evalFunc (codeMat 128 + codeMat 12) M = 0) ∧ evalFunc (codeMat 64) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] (step99o120MatrixCodeNat M) hbool
  rwa [step99o120_codeMat_matrixCode] at hspan

private theorem step99o120s0_contain :
    step99o120ActualSource0 ≤ o55W := by
  apply step99o120_spanCodes_le_of_gens [272, 132, 32, 12, 2, 1] o55W
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

theorem step99o120s0Dispatch :
    QuotientRankAtLeast (o120SourceU ⟨0, by omega⟩) 14 :=
  quotientRankAtLeast_mono (le_trans step99o120s0_sourceU_le step99o120s0_contain) step99_orbit55_lb14_unconditional

-- Source 1 (row 1): orbit 55, lb 14
def step99o120ActualSource1 : Submodule F2 Mat3 := spanCodes [272, 148, 32, 12, 2, 1]

private theorem step99o120s1_sourceU_le :
    (o120SourceU ⟨1, by omega⟩) ≤ step99o120ActualSource1 := by
  intro M hM
  have hbool : spanContainsCodeCore [272, 148, 32, 12, 2, 1] (step99o120MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 272 + codeMat 12) ⊓ kerEvalFunc (codeMat 128 + codeMat 12)) ⊓ kerEvalFunc (codeMat 64)) at hM
    change ((evalFunc (codeMat 272 + codeMat 12) M = 0 ∧ evalFunc (codeMat 128 + codeMat 12) M = 0) ∧ evalFunc (codeMat 64) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 148, 32, 12, 2, 1] (step99o120MatrixCodeNat M) hbool
  rwa [step99o120_codeMat_matrixCode] at hspan

private theorem step99o120s1_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o120s1_targetSpan_le_action :
    step99o120ActualSource1 ≤ actionW (codeMat 401) (codeMat 273) o55W := by
  apply step99o120_spanCodes_le_of_gens [272, 148, 32, 12, 2, 1]
    (actionW (codeMat 401) (codeMat 273) o55W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 304 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 304 (by decide)
    have hact : actionA (codeMat 401) (codeMat 273) (codeMat 304) = codeMat 272 := by
      unfold actionA
      rw [step99o120s1_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 304 * (codeMat 273 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 132 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 132 (by decide)
    have hact : actionA (codeMat 401) (codeMat 273) (codeMat 132) = codeMat 148 := by
      unfold actionA
      rw [step99o120s1_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 132 * (codeMat 273 : Mat3).transpose = codeMat 148
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 32 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 401) (codeMat 273) (codeMat 32) = codeMat 32 := by
      unfold actionA
      rw [step99o120s1_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 32 * (codeMat 273 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 12 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 12 (by decide)
    have hact : actionA (codeMat 401) (codeMat 273) (codeMat 12) = codeMat 12 := by
      unfold actionA
      rw [step99o120s1_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 12 * (codeMat 273 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 401) (codeMat 273) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step99o120s1_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 401) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step99o120s1_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact

theorem step99o120s1Dispatch :
    QuotientRankAtLeast (o120SourceU ⟨1, by omega⟩) 14 := by
  have hP : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 401) (codeMat 273) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 401) (codeMat 273) hP hQ o55W 14 step99_orbit55_lb14_unconditional
  have hMono : QuotientRankAtLeast step99o120ActualSource1 14 :=
    quotientRankAtLeast_mono step99o120s1_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o120s1_sourceU_le hMono

-- Source 2 (row 2): orbit 55, lb 14
def step99o120ActualSource2 : Submodule F2 Mat3 := spanCodes [272, 196, 32, 12, 2, 1]

private theorem step99o120s2_sourceU_le :
    (o120SourceU ⟨2, by omega⟩) ≤ step99o120ActualSource2 := by
  intro M hM
  have hbool : spanContainsCodeCore [272, 196, 32, 12, 2, 1] (step99o120MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 272) ⊓ kerEvalFunc (codeMat 128 + codeMat 12)) ⊓ kerEvalFunc (codeMat 64 + codeMat 12)) at hM
    change ((evalFunc (codeMat 272) M = 0 ∧ evalFunc (codeMat 128 + codeMat 12) M = 0) ∧ evalFunc (codeMat 64 + codeMat 12) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 196, 32, 12, 2, 1] (step99o120MatrixCodeNat M) hbool
  rwa [step99o120_codeMat_matrixCode] at hspan

private theorem step99o120s2_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = (codeMat 275 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * (codeMat 275 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o120s2_targetSpan_le_action :
    step99o120ActualSource2 ≤ actionW (codeMat 337) (codeMat 275) o55W := by
  apply step99o120_spanCodes_le_of_gens [272, 196, 32, 12, 2, 1]
    (actionW (codeMat 337) (codeMat 275) o55W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 284 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 284 (by decide)
    have hact : actionA (codeMat 337) (codeMat 275) (codeMat 284) = codeMat 272 := by
      unfold actionA
      rw [step99o120s2_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 284 * (codeMat 275 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 134 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 134 (by decide)
    have hact : actionA (codeMat 337) (codeMat 275) (codeMat 134) = codeMat 196 := by
      unfold actionA
      rw [step99o120s2_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 134 * (codeMat 275 : Mat3).transpose = codeMat 196
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 32 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 337) (codeMat 275) (codeMat 32) = codeMat 32 := by
      unfold actionA
      rw [step99o120s2_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 32 * (codeMat 275 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 12 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 12 (by decide)
    have hact : actionA (codeMat 337) (codeMat 275) (codeMat 12) = codeMat 12 := by
      unfold actionA
      rw [step99o120s2_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 12 * (codeMat 275 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 337) (codeMat 275) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [step99o120s2_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 3 * (codeMat 275 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 337) (codeMat 275) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step99o120s2_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 1 * (codeMat 275 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact

theorem step99o120s2Dispatch :
    QuotientRankAtLeast (o120SourceU ⟨2, by omega⟩) 14 := by
  have hP : Invertible (codeMat 337 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 337) (codeMat 275) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 337) (codeMat 275) hP hQ o55W 14 step99_orbit55_lb14_unconditional
  have hMono : QuotientRankAtLeast step99o120ActualSource2 14 :=
    quotientRankAtLeast_mono step99o120s2_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o120s2_sourceU_le hMono

-- Source 3 (row 3): orbit 55, lb 14
def step99o120ActualSource3 : Submodule F2 Mat3 := spanCodes [272, 208, 32, 12, 2, 1]

private theorem step99o120s3_sourceU_le :
    (o120SourceU ⟨3, by omega⟩) ≤ step99o120ActualSource3 := by
  intro M hM
  have hbool : spanContainsCodeCore [272, 208, 32, 12, 2, 1] (step99o120MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 272 + codeMat 64) ⊓ kerEvalFunc (codeMat 128 + codeMat 64)) ⊓ kerEvalFunc (codeMat 12)) at hM
    change ((evalFunc (codeMat 272 + codeMat 64) M = 0 ∧ evalFunc (codeMat 128 + codeMat 64) M = 0) ∧ evalFunc (codeMat 12) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 208, 32, 12, 2, 1] (step99o120MatrixCodeNat M) hbool
  rwa [step99o120_codeMat_matrixCode] at hspan

private theorem step99o120s3_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = (codeMat 275 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * (codeMat 275 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o120s3_targetSpan_le_action :
    step99o120ActualSource3 ≤ actionW (codeMat 465) (codeMat 275) o55W := by
  apply step99o120_spanCodes_le_of_gens [272, 208, 32, 12, 2, 1]
    (actionW (codeMat 465) (codeMat 275) o55W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 316 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 316 (by decide)
    have hact : actionA (codeMat 465) (codeMat 275) (codeMat 316) = codeMat 272 := by
      unfold actionA
      rw [step99o120s3_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 316 * (codeMat 275 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 138 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 138 (by decide)
    have hact : actionA (codeMat 465) (codeMat 275) (codeMat 138) = codeMat 208 := by
      unfold actionA
      rw [step99o120s3_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 138 * (codeMat 275 : Mat3).transpose = codeMat 208
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 32 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 465) (codeMat 275) (codeMat 32) = codeMat 32 := by
      unfold actionA
      rw [step99o120s3_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 32 * (codeMat 275 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 12 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 12 (by decide)
    have hact : actionA (codeMat 465) (codeMat 275) (codeMat 12) = codeMat 12 := by
      unfold actionA
      rw [step99o120s3_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 12 * (codeMat 275 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 465) (codeMat 275) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [step99o120s3_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 3 * (codeMat 275 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 465) (codeMat 275) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step99o120s3_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 1 * (codeMat 275 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact

theorem step99o120s3Dispatch :
    QuotientRankAtLeast (o120SourceU ⟨3, by omega⟩) 14 := by
  have hP : Invertible (codeMat 465 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 465) (codeMat 275) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 465) (codeMat 275) hP hQ o55W 14 step99_orbit55_lb14_unconditional
  have hMono : QuotientRankAtLeast step99o120ActualSource3 14 :=
    quotientRankAtLeast_mono step99o120s3_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o120s3_sourceU_le hMono

-- Source 4 (row 6): orbit 32, lb 12
def step99o120ActualSource4 : Submodule F2 Mat3 := spanCodes [256, 32, 16, 12, 2, 1]

private theorem step99o120s4_sourceU_le :
    (o120SourceU ⟨4, by omega⟩) ≤ step99o120ActualSource4 := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 32, 16, 12, 2, 1] (step99o120MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 128) ⊓ kerEvalFunc (codeMat 64)) ⊓ kerEvalFunc (codeMat 12)) at hM
    change ((evalFunc (codeMat 128) M = 0 ∧ evalFunc (codeMat 64) M = 0) ∧ evalFunc (codeMat 12) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 32, 16, 12, 2, 1] (step99o120MatrixCodeNat M) hbool
  rwa [step99o120_codeMat_matrixCode] at hspan

private theorem step99o120s4_QtInv :
    (codeMat 98 : Mat3).transpose⁻¹ = (codeMat 140 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 98 : Mat3).transpose * (codeMat 140 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o120s4_targetSpan_le_action :
    step99o120ActualSource4 ≤ actionW (codeMat 266) (codeMat 98) monoW_32 := by
  apply step99o120_spanCodes_le_of_gens [256, 32, 16, 12, 2, 1]
    (actionW (codeMat 266) (codeMat 98) monoW_32)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 128 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 128) = codeMat 256 := by
      unfold actionA
      rw [step99o120s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 128 * (codeMat 140 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 2) = codeMat 32 := by
      unfold actionA
      rw [step99o120s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 140 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step99o120s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 140 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 20 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 20 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 20) = codeMat 12 := by
      unfold actionA
      rw [step99o120s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 20 * (codeMat 140 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 8) = codeMat 2 := by
      unfold actionA
      rw [step99o120s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 140 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step99o120s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 140 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact

theorem step99o120s4Dispatch :
    QuotientRankAtLeast (o120SourceU ⟨4, by omega⟩) 12 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 98) monoW_32) 12 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 98) hP hQ monoW_32 12 step99_mono_32_lb12
  have hMono : QuotientRankAtLeast step99o120ActualSource4 12 :=
    quotientRankAtLeast_mono step99o120s4_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o120s4_sourceU_le hMono

-- Source 5 (row 7): orbit 32, lb 12
def step99o120ActualSource5 : Submodule F2 Mat3 := spanCodes [260, 32, 20, 12, 2, 1]

private theorem step99o120s5_sourceU_le :
    (o120SourceU ⟨5, by omega⟩) ≤ step99o120ActualSource5 := by
  intro M hM
  have hbool : spanContainsCodeCore [260, 32, 20, 12, 2, 1] (step99o120MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 272 + codeMat 12) ⊓ kerEvalFunc (codeMat 128)) ⊓ kerEvalFunc (codeMat 64)) at hM
    change ((evalFunc (codeMat 272 + codeMat 12) M = 0 ∧ evalFunc (codeMat 128) M = 0) ∧ evalFunc (codeMat 64) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 32, 20, 12, 2, 1] (step99o120MatrixCodeNat M) hbool
  rwa [step99o120_codeMat_matrixCode] at hspan

private theorem step99o120s5_QtInv :
    (codeMat 226 : Mat3).transpose⁻¹ = (codeMat 141 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 226 : Mat3).transpose * (codeMat 141 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o120s5_targetSpan_le_action :
    step99o120ActualSource5 ≤ actionW (codeMat 330) (codeMat 226) monoW_32 := by
  apply step99o120_spanCodes_le_of_gens [260, 32, 20, 12, 2, 1]
    (actionW (codeMat 330) (codeMat 226) monoW_32)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 128 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 330) (codeMat 226) (codeMat 128) = codeMat 260 := by
      unfold actionA
      rw [step99o120s5_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 128 * (codeMat 141 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 330) (codeMat 226) (codeMat 2) = codeMat 32 := by
      unfold actionA
      rw [step99o120s5_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 2 * (codeMat 141 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 21 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 21 (by decide)
    have hact : actionA (codeMat 330) (codeMat 226) (codeMat 21) = codeMat 20 := by
      unfold actionA
      rw [step99o120s5_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 21 * (codeMat 141 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 20 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 20 (by decide)
    have hact : actionA (codeMat 330) (codeMat 226) (codeMat 20) = codeMat 12 := by
      unfold actionA
      rw [step99o120s5_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 20 * (codeMat 141 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 40 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 330) (codeMat 226) (codeMat 40) = codeMat 2 := by
      unfold actionA
      rw [step99o120s5_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 40 * (codeMat 141 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 330) (codeMat 226) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step99o120s5_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 32 * (codeMat 141 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact

theorem step99o120s5Dispatch :
    QuotientRankAtLeast (o120SourceU ⟨5, by omega⟩) 12 := by
  have hP : Invertible (codeMat 330 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 226 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 330) (codeMat 226) monoW_32) 12 :=
    @quotientRankAtLeast_action (codeMat 330) (codeMat 226) hP hQ monoW_32 12 step99_mono_32_lb12
  have hMono : QuotientRankAtLeast step99o120ActualSource5 12 :=
    quotientRankAtLeast_mono step99o120s5_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o120s5_sourceU_le hMono

-- Source 6 (row 14): orbit 10, lb 12
def step99o120ActualSource6 : Submodule F2 Mat3 := spanCodes [272, 128, 64, 32, 12, 2, 1]

private theorem step99o120s6_sourceU_le :
    (o120SourceU ⟨6, by omega⟩) ≤ step99o120ActualSource6 := by
  intro M hM
  have hbool : spanContainsCodeCore [272, 128, 64, 32, 12, 2, 1] (step99o120MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 272) ⊓ kerEvalFunc (codeMat 12)) at hM
    change (evalFunc (codeMat 272) M = 0 ∧ evalFunc (codeMat 12) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 128, 64, 32, 12, 2, 1] (step99o120MatrixCodeNat M) hbool
  rwa [step99o120_codeMat_matrixCode] at hspan

private theorem step99o120s6_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o120s6_targetSpan_le_action :
    step99o120ActualSource6 ≤ actionW (codeMat 140) (codeMat 266) orbit10W := by
  apply step99o120_spanCodes_le_of_gens [272, 128, 64, 32, 12, 2, 1]
    (actionW (codeMat 140) (codeMat 266) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 68 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 140) (codeMat 266) (codeMat 68) = codeMat 272 := by
      unfold actionA
      rw [step99o120s6_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 68 * (codeMat 266 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 140) (codeMat 266) (codeMat 1) = codeMat 128 := by
      unfold actionA
      rw [step99o120s6_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 140) (codeMat 266) (codeMat 2) = codeMat 64 := by
      unfold actionA
      rw [step99o120s6_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 2 * (codeMat 266 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 140) (codeMat 266) (codeMat 256) = codeMat 32 := by
      unfold actionA
      rw [step99o120s6_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 256 * (codeMat 266 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 140) (codeMat 266) (codeMat 160) = codeMat 12 := by
      unfold actionA
      rw [step99o120s6_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 160 * (codeMat 266 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 140) (codeMat 266) (codeMat 8) = codeMat 2 := by
      unfold actionA
      rw [step99o120s6_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 8 * (codeMat 266 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 140) (codeMat 266) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step99o120s6_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 16 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact

theorem step99o120s6Dispatch :
    QuotientRankAtLeast (o120SourceU ⟨6, by omega⟩) 12 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 266) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 266) hP hQ orbit10W 12 orbit10_lb12
  have hMono : QuotientRankAtLeast step99o120ActualSource6 12 :=
    quotientRankAtLeast_mono step99o120s6_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o120s6_sourceU_le hMono

-- Source 7 (row 28): orbit 10, lb 12
def step99o120ActualSource7 : Submodule F2 Mat3 := spanCodes [272, 144, 68, 32, 12, 2, 1]

private theorem step99o120s7_sourceU_le :
    (o120SourceU ⟨7, by omega⟩) ≤ step99o120ActualSource7 := by
  intro M hM
  have hbool : spanContainsCodeCore [272, 144, 68, 32, 12, 2, 1] (step99o120MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 272 + codeMat 128) ⊓ kerEvalFunc (codeMat 64 + codeMat 12)) at hM
    change (evalFunc (codeMat 272 + codeMat 128) M = 0 ∧ evalFunc (codeMat 64 + codeMat 12) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 144, 68, 32, 12, 2, 1] (step99o120MatrixCodeNat M) hbool
  rwa [step99o120_codeMat_matrixCode] at hspan

private theorem step99o120s7_QtInv :
    (codeMat 270 : Mat3).transpose⁻¹ = (codeMat 298 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 270 : Mat3).transpose * (codeMat 298 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o120s7_targetSpan_le_action :
    step99o120ActualSource7 ≤ actionW (codeMat 270) (codeMat 270) orbit10W := by
  apply step99o120_spanCodes_le_of_gens [272, 144, 68, 32, 12, 2, 1]
    (actionW (codeMat 270) (codeMat 270) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 257 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 257 (by decide)
    have hact : actionA (codeMat 270) (codeMat 270) (codeMat 257) = codeMat 272 := by
      unfold actionA
      rw [step99o120s7_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 257 * (codeMat 298 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 270) (codeMat 270) (codeMat 1) = codeMat 144 := by
      unfold actionA
      rw [step99o120s7_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 1 * (codeMat 298 : Mat3).transpose = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 168 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 168 (by decide)
    have hact : actionA (codeMat 270) (codeMat 270) (codeMat 168) = codeMat 68 := by
      unfold actionA
      rw [step99o120s7_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 168 * (codeMat 298 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 325 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 325 (by decide)
    have hact : actionA (codeMat 270) (codeMat 270) (codeMat 325) = codeMat 32 := by
      unfold actionA
      rw [step99o120s7_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 325 * (codeMat 298 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 170 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 170 (by decide)
    have hact : actionA (codeMat 270) (codeMat 270) (codeMat 170) = codeMat 12 := by
      unfold actionA
      rw [step99o120s7_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 170 * (codeMat 298 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 270) (codeMat 270) (codeMat 8) = codeMat 2 := by
      unfold actionA
      rw [step99o120s7_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 8 * (codeMat 298 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 270) (codeMat 270) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step99o120s7_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 16 * (codeMat 298 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact

theorem step99o120s7Dispatch :
    QuotientRankAtLeast (o120SourceU ⟨7, by omega⟩) 12 := by
  have hP : Invertible (codeMat 270 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 270 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 270) (codeMat 270) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 270) (codeMat 270) hP hQ orbit10W 12 orbit10_lb12
  have hMono : QuotientRankAtLeast step99o120ActualSource7 12 :=
    quotientRankAtLeast_mono step99o120s7_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o120s7_sourceU_le hMono

-- Source 8 (row 36): orbit 5, lb 9
def step99o120ActualSource8 : Submodule F2 Mat3 := spanCodes [272, 80, 32, 8, 4, 2, 1]

private theorem step99o120s8_sourceU_le :
    (o120SourceU ⟨8, by omega⟩) ≤ step99o120ActualSource8 := by
  intro M hM
  have hbool : spanContainsCodeCore [272, 80, 32, 8, 4, 2, 1] (step99o120MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 272 + codeMat 64) ⊓ kerEvalFunc (codeMat 128)) at hM
    change (evalFunc (codeMat 272 + codeMat 64) M = 0 ∧ evalFunc (codeMat 128) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 80, 32, 8, 4, 2, 1] (step99o120MatrixCodeNat M) hbool
  rwa [step99o120_codeMat_matrixCode] at hspan

private theorem step99o120s8_QtInv :
    (codeMat 172 : Mat3).transpose⁻¹ = (codeMat 99 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 172 : Mat3).transpose * (codeMat 99 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o120s8_targetSpan_le_action :
    step99o120ActualSource8 ≤ actionW (codeMat 273) (codeMat 172) orbit5W := by
  apply step99o120_spanCodes_le_of_gens [272, 80, 32, 8, 4, 2, 1]
    (actionW (codeMat 273) (codeMat 172) orbit5W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 224 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 224 (by decide)
    have hact : actionA (codeMat 273) (codeMat 172) (codeMat 224) = codeMat 272 := by
      unfold actionA
      rw [step99o120s8_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 224 * (codeMat 99 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 160 (by decide)
    have hact : actionA (codeMat 273) (codeMat 172) (codeMat 160) = codeMat 80 := by
      unfold actionA
      rw [step99o120s8_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 160 * (codeMat 99 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 24 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 24 (by decide)
    have hact : actionA (codeMat 273) (codeMat 172) (codeMat 24) = codeMat 32 := by
      unfold actionA
      rw [step99o120s8_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 24 * (codeMat 99 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 16 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 16 (by decide)
    have hact : actionA (codeMat 273) (codeMat 172) (codeMat 16) = codeMat 8 := by
      unfold actionA
      rw [step99o120s8_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 16 * (codeMat 99 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 3 (by decide)
    have hact : actionA (codeMat 273) (codeMat 172) (codeMat 3) = codeMat 4 := by
      unfold actionA
      rw [step99o120s8_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 3 * (codeMat 99 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 4 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 4 (by decide)
    have hact : actionA (codeMat 273) (codeMat 172) (codeMat 4) = codeMat 2 := by
      unfold actionA
      rw [step99o120s8_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 4 * (codeMat 99 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 172) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step99o120s8_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 99 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o120_codeMat_mem_actionW_of_witness hw hact

theorem step99o120s8Dispatch :
    QuotientRankAtLeast (o120SourceU ⟨8, by omega⟩) 9 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 172 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 172) orbit5W) 9 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 172) hP hQ orbit5W 9 orbit5_lb9
  have hMono : QuotientRankAtLeast step99o120ActualSource8 9 :=
    quotientRankAtLeast_mono step99o120s8_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o120s8_sourceU_le hMono

theorem step99o120_all_dispatch (i : Fin 9) :
    QuotientRankAtLeast (o120SourceU i) (o120SourceLb i) := by
  fin_cases i
  · exact step99o120s0Dispatch
  · exact step99o120s1Dispatch
  · exact step99o120s2Dispatch
  · exact step99o120s3Dispatch
  · exact step99o120s4Dispatch
  · exact step99o120s5Dispatch
  · exact step99o120s6Dispatch
  · exact step99o120s7Dispatch
  · exact step99o120s8Dispatch

theorem step99_orbit120_lb15_unconditional :
    QuotientRankAtLeast o120W 15 :=
  o120Lb15 step99o120_all_dispatch

end QiushiMatmul
