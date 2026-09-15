import QiushiCodeSpanCore
import QiushiFlattenSeeds
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiStep98Orbit150Consumer
import QiushiStep99Mono3032
import QiushiStep99Orbit34Dispatch
import QiushiStep99Orbit55Dispatch
import QiushiStep99Orbit65Dispatch
import QiushiTransposeTransport

set_option maxHeartbeats 800000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem step99o150_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step99o150MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step99o150_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step99o150MatrixCodeNat M) = M := by decide

lemma step99o150_codeMat_matrixCode (M : Mat3) :
    codeMat (step99o150MatrixCodeNat M) = M :=
  step99o150_codeMat_matrixCode_all M

private theorem step99o150_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step99o150_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

private theorem step99o150_codeMat_mem_transposeW_of_witness
    {V : Submodule F2 Mat3} {pre tpre : Nat}
    (h_mem : codeMat tpre ∈ V)
    (h_trans : (codeMat tpre : Mat3).transpose = codeMat pre) :
    codeMat pre ∈ transposeW V := by
  change ∃ X, X ∈ V ∧ transposeLinearMap X = codeMat pre
  exact ⟨codeMat tpre, h_mem, h_trans⟩

-- Source 0 (row 1): orbit 65, lb 15
def step99o150ActualSource0 : Submodule F2 Mat3 := spanCodes [258, 162, 68, 16, 10, 1]

private theorem step99o150s0_sourceU_le :
    (o150SourceU ⟨0, by omega⟩) ≤ step99o150ActualSource0 := by
  intro M hM
  have hbool : spanContainsCodeCore [258, 162, 68, 16, 10, 1] (step99o150MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 266 + codeMat 32) ⊓ kerEvalFunc (codeMat 128 + codeMat 32)) ⊓ kerEvalFunc (codeMat 68)) at hM
    change ((evalFunc (codeMat 266 + codeMat 32) M = 0 ∧ evalFunc (codeMat 128 + codeMat 32) M = 0) ∧ evalFunc (codeMat 68) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 162, 68, 16, 10, 1] (step99o150MatrixCodeNat M) hbool
  rwa [step99o150_codeMat_matrixCode] at hspan

private theorem step99o150s0_QtInv :
    (codeMat 309 : Mat3).transpose⁻¹ = (codeMat 309 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 309 : Mat3).transpose * (codeMat 309 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o150s0_targetSpan_le_action :
    step99o150ActualSource0 ≤ actionW (codeMat 401) (codeMat 309) o65W := by
  apply step99o150_spanCodes_le_of_gens [258, 162, 68, 16, 10, 1]
    (actionW (codeMat 401) (codeMat 309) o65W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 506 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 506 (by decide)
    have hact : actionA (codeMat 401) (codeMat 309) (codeMat 506) = codeMat 258 := by
      unfold actionA
      rw [step99o150s0_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 506 * (codeMat 309 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 170 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 170 (by decide)
    have hact : actionA (codeMat 401) (codeMat 309) (codeMat 170) = codeMat 162 := by
      unfold actionA
      rw [step99o150s0_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 170 * (codeMat 309 : Mat3).transpose = codeMat 162
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 79 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 79 (by decide)
    have hact : actionA (codeMat 401) (codeMat 309) (codeMat 79) = codeMat 68 := by
      unfold actionA
      rw [step99o150s0_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 79 * (codeMat 309 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 16 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 401) (codeMat 309) (codeMat 16) = codeMat 16 := by
      unfold actionA
      rw [step99o150s0_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 16 * (codeMat 309 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 10 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 401) (codeMat 309) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step99o150s0_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 10 * (codeMat 309 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 401) (codeMat 309) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step99o150s0_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 1 * (codeMat 309 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_actionW_of_witness hw hact

theorem step99o150s0Dispatch :
    QuotientRankAtLeast (o150SourceU ⟨0, by omega⟩) 15 := by
  have hP : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 309 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 401) (codeMat 309) o65W) 15 :=
    @quotientRankAtLeast_action (codeMat 401) (codeMat 309) hP hQ o65W 15 step99_orbit65_lb15_unconditional
  have hMono : QuotientRankAtLeast step99o150ActualSource0 15 :=
    quotientRankAtLeast_mono step99o150s0_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o150s0_sourceU_le hMono

-- Source 1 (row 2): orbit 65, lb 15
def step99o150ActualSource1 : Submodule F2 Mat3 := spanCodes [258, 164, 68, 16, 10, 1]

private theorem step99o150s1_sourceU_le :
    (o150SourceU ⟨1, by omega⟩) ≤ step99o150ActualSource1 := by
  intro M hM
  have hbool : spanContainsCodeCore [258, 164, 68, 16, 10, 1] (step99o150MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 266) ⊓ kerEvalFunc (codeMat 128 + codeMat 32)) ⊓ kerEvalFunc (codeMat 68 + codeMat 32)) at hM
    change ((evalFunc (codeMat 266) M = 0 ∧ evalFunc (codeMat 128 + codeMat 32) M = 0) ∧ evalFunc (codeMat 68 + codeMat 32) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 164, 68, 16, 10, 1] (step99o150MatrixCodeNat M) hbool
  rwa [step99o150_codeMat_matrixCode] at hspan

private theorem step99o150s1_QtInv :
    (codeMat 419 : Mat3).transpose⁻¹ = (codeMat 183 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 419 : Mat3).transpose * (codeMat 183 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o150s1_targetSpan_le_action :
    step99o150ActualSource1 ≤ actionW (codeMat 177) (codeMat 419) o65W := by
  apply step99o150_spanCodes_le_of_gens [258, 164, 68, 16, 10, 1]
    (actionW (codeMat 177) (codeMat 419) o65W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 437 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 437 (by decide)
    have hact : actionA (codeMat 177) (codeMat 419) (codeMat 437) = codeMat 258 := by
      unfold actionA
      rw [step99o150s1_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 437 * (codeMat 183 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 238 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 238 (by decide)
    have hact : actionA (codeMat 177) (codeMat 419) (codeMat 238) = codeMat 164 := by
      unfold actionA
      rw [step99o150s1_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 238 * (codeMat 183 : Mat3).transpose = codeMat 164
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 78 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 78 (by decide)
    have hact : actionA (codeMat 177) (codeMat 419) (codeMat 78) = codeMat 68 := by
      unfold actionA
      rw [step99o150s1_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 78 * (codeMat 183 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 320 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 320 (by decide)
    have hact : actionA (codeMat 177) (codeMat 419) (codeMat 320) = codeMat 16 := by
      unfold actionA
      rw [step99o150s1_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 320 * (codeMat 183 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 69 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 69 (by decide)
    have hact : actionA (codeMat 177) (codeMat 419) (codeMat 69) = codeMat 10 := by
      unfold actionA
      rw [step99o150s1_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 69 * (codeMat 183 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 419) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step99o150s1_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * (codeMat 183 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_actionW_of_witness hw hact

theorem step99o150s1Dispatch :
    QuotientRankAtLeast (o150SourceU ⟨1, by omega⟩) 15 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 419 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 419) o65W) 15 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 419) hP hQ o65W 15 step99_orbit65_lb15_unconditional
  have hMono : QuotientRankAtLeast step99o150ActualSource1 15 :=
    quotientRankAtLeast_mono step99o150s1_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o150s1_sourceU_le hMono

-- Source 2 (row 4): orbit 34, lb 14
def step99o150ActualSource2 : Submodule F2 Mat3 := spanCodes [258, 64, 16, 10, 4, 1]

private theorem step99o150s2_sourceU_le :
    (o150SourceU ⟨2, by omega⟩) ≤ step99o150ActualSource2 := by
  intro M hM
  have hbool : spanContainsCodeCore [258, 64, 16, 10, 4, 1] (step99o150MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 266) ⊓ kerEvalFunc (codeMat 128)) ⊓ kerEvalFunc (codeMat 32)) at hM
    change ((evalFunc (codeMat 266) M = 0 ∧ evalFunc (codeMat 128) M = 0) ∧ evalFunc (codeMat 32) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 64, 16, 10, 4, 1] (step99o150MatrixCodeNat M) hbool
  rwa [step99o150_codeMat_matrixCode] at hspan

private theorem step99o150s2_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o150s2_targetSpan_le_action :
    step99o150ActualSource2 ≤ actionW (codeMat 161) (codeMat 161) o34W := by
  apply step99o150_spanCodes_le_of_gens [258, 64, 16, 10, 4, 1]
    (actionW (codeMat 161) (codeMat 161) o34W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 20 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 20 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 20) = codeMat 258 := by
      unfold actionA
      rw [step99o150s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 20 * (codeMat 161 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 8 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 8) = codeMat 64 := by
      unfold actionA
      rw [step99o150s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 8 * (codeMat 161 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 256 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 256) = codeMat 16 := by
      unfold actionA
      rw [step99o150s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 256 * (codeMat 161 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 68 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 68 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 68) = codeMat 10 := by
      unfold actionA
      rw [step99o150s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 68 * (codeMat 161 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 2) = codeMat 4 := by
      unfold actionA
      rw [step99o150s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 161 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step99o150s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_actionW_of_witness hw hact

theorem step99o150s2Dispatch :
    QuotientRankAtLeast (o150SourceU ⟨2, by omega⟩) 14 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 161) o34W) 14 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 161) hP hQ o34W 14 step99_orbit34_lb14_unconditional
  have hMono : QuotientRankAtLeast step99o150ActualSource2 14 :=
    quotientRankAtLeast_mono step99o150s2_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o150s2_sourceU_le hMono

-- Source 3 (row 6): orbit 55, lb 14
def step99o150ActualSource3 : Submodule F2 Mat3 := spanCodes [258, 68, 34, 16, 10, 1]

private theorem step99o150s3_sourceU_le :
    (o150SourceU ⟨3, by omega⟩) ≤ step99o150ActualSource3 := by
  intro M hM
  have hbool : spanContainsCodeCore [258, 68, 34, 16, 10, 1] (step99o150MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 266 + codeMat 32) ⊓ kerEvalFunc (codeMat 128)) ⊓ kerEvalFunc (codeMat 68)) at hM
    change ((evalFunc (codeMat 266 + codeMat 32) M = 0 ∧ evalFunc (codeMat 128) M = 0) ∧ evalFunc (codeMat 68) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 68, 34, 16, 10, 1] (step99o150MatrixCodeNat M) hbool
  rwa [step99o150_codeMat_matrixCode] at hspan

private theorem step99o150s3_QtInv :
    (codeMat 354 : Mat3).transpose⁻¹ = (codeMat 142 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 354 : Mat3).transpose * (codeMat 142 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o150s3_targetSpan_le_action :
    step99o150ActualSource3 ≤ actionW (codeMat 330) (codeMat 354) o55W := by
  apply step99o150_spanCodes_le_of_gens [258, 68, 34, 16, 10, 1]
    (actionW (codeMat 330) (codeMat 354) o55W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 440 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 440 (by decide)
    have hact : actionA (codeMat 330) (codeMat 354) (codeMat 440) = codeMat 258 := by
      unfold actionA
      rw [step99o150s3_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 440 * (codeMat 142 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 272 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 272 (by decide)
    have hact : actionA (codeMat 330) (codeMat 354) (codeMat 272) = codeMat 68 := by
      unfold actionA
      rw [step99o150s3_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 272 * (codeMat 142 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 14 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 14 (by decide)
    have hact : actionA (codeMat 330) (codeMat 354) (codeMat 14) = codeMat 34 := by
      unfold actionA
      rw [step99o150s3_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 14 * (codeMat 142 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 330) (codeMat 354) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step99o150s3_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 1 * (codeMat 142 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 12 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 12 (by decide)
    have hact : actionA (codeMat 330) (codeMat 354) (codeMat 12) = codeMat 10 := by
      unfold actionA
      rw [step99o150s3_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 12 * (codeMat 142 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 330) (codeMat 354) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step99o150s3_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 32 * (codeMat 142 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_actionW_of_witness hw hact

theorem step99o150s3Dispatch :
    QuotientRankAtLeast (o150SourceU ⟨3, by omega⟩) 14 := by
  have hP : Invertible (codeMat 330 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 354 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 330) (codeMat 354) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 330) (codeMat 354) hP hQ o55W 14 step99_orbit55_lb14_unconditional
  have hMono : QuotientRankAtLeast step99o150ActualSource3 14 :=
    quotientRankAtLeast_mono step99o150s3_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o150s3_sourceU_le hMono

-- Source 4 (row 7): orbit 55, lb 14
def step99o150ActualSource4 : Submodule F2 Mat3 := spanCodes [258, 68, 36, 16, 10, 1]

private theorem step99o150s4_sourceU_le :
    (o150SourceU ⟨4, by omega⟩) ≤ step99o150ActualSource4 := by
  intro M hM
  have hbool : spanContainsCodeCore [258, 68, 36, 16, 10, 1] (step99o150MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 266) ⊓ kerEvalFunc (codeMat 128)) ⊓ kerEvalFunc (codeMat 68 + codeMat 32)) at hM
    change ((evalFunc (codeMat 266) M = 0 ∧ evalFunc (codeMat 128) M = 0) ∧ evalFunc (codeMat 68 + codeMat 32) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 68, 36, 16, 10, 1] (step99o150MatrixCodeNat M) hbool
  rwa [step99o150_codeMat_matrixCode] at hspan

private theorem step99o150s4_QtInv :
    (codeMat 226 : Mat3).transpose⁻¹ = (codeMat 141 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 226 : Mat3).transpose * (codeMat 141 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o150s4_targetSpan_le_action :
    step99o150ActualSource4 ≤ actionW (codeMat 267) (codeMat 226) o55W := by
  apply step99o150_spanCodes_le_of_gens [258, 68, 36, 16, 10, 1]
    (actionW (codeMat 267) (codeMat 226) o55W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 168 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 168 (by decide)
    have hact : actionA (codeMat 267) (codeMat 226) (codeMat 168) = codeMat 258 := by
      unfold actionA
      rw [step99o150s4_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 168 * (codeMat 141 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 272 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 272 (by decide)
    have hact : actionA (codeMat 267) (codeMat 226) (codeMat 272) = codeMat 68 := by
      unfold actionA
      rw [step99o150s4_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 272 * (codeMat 141 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 267) (codeMat 226) (codeMat 2) = codeMat 36 := by
      unfold actionA
      rw [step99o150s4_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 2 * (codeMat 141 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 45 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 45 (by decide)
    have hact : actionA (codeMat 267) (codeMat 226) (codeMat 45) = codeMat 16 := by
      unfold actionA
      rw [step99o150s4_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 45 * (codeMat 141 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 12 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 12 (by decide)
    have hact : actionA (codeMat 267) (codeMat 226) (codeMat 12) = codeMat 10 := by
      unfold actionA
      rw [step99o150s4_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 12 * (codeMat 141 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 267) (codeMat 226) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step99o150s4_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 32 * (codeMat 141 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_actionW_of_witness hw hact

theorem step99o150s4Dispatch :
    QuotientRankAtLeast (o150SourceU ⟨4, by omega⟩) 14 := by
  have hP : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 226 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 267) (codeMat 226) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 267) (codeMat 226) hP hQ o55W 14 step99_orbit55_lb14_unconditional
  have hMono : QuotientRankAtLeast step99o150ActualSource4 14 :=
    quotientRankAtLeast_mono step99o150s4_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o150s4_sourceU_le hMono

-- Source 5 (row 10): orbit 55, lb 14
def step99o150ActualSource5 : Submodule F2 Mat3 := spanCodes [258, 130, 68, 16, 10, 1]

private theorem step99o150s5_sourceU_le :
    (o150SourceU ⟨5, by omega⟩) ≤ step99o150ActualSource5 := by
  intro M hM
  have hbool : spanContainsCodeCore [258, 130, 68, 16, 10, 1] (step99o150MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 266 + codeMat 128) ⊓ kerEvalFunc (codeMat 68)) ⊓ kerEvalFunc (codeMat 32)) at hM
    change ((evalFunc (codeMat 266 + codeMat 128) M = 0 ∧ evalFunc (codeMat 68) M = 0) ∧ evalFunc (codeMat 32) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 130, 68, 16, 10, 1] (step99o150MatrixCodeNat M) hbool
  rwa [step99o150_codeMat_matrixCode] at hspan

private theorem step99o150s5_QtInv :
    (codeMat 354 : Mat3).transpose⁻¹ = (codeMat 142 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 354 : Mat3).transpose * (codeMat 142 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o150s5_targetSpan_le_transposeAction :
    step99o150ActualSource5 ≤ transposeW (actionW (codeMat 330) (codeMat 354) o55W) := by
  apply step99o150_spanCodes_le_of_gens [258, 130, 68, 16, 10, 1]
    (transposeW (actionW (codeMat 330) (codeMat 354) o55W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    -- g=258, g^T=264; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 436 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 436 (by decide)
    have hact : actionA (codeMat 330) (codeMat 354) (codeMat 436) = codeMat 264 := by
      unfold actionA
      rw [step99o150s5_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 436 * (codeMat 142 : Mat3).transpose = codeMat 264
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 264 ∈ actionW (codeMat 330) (codeMat 354) o55W :=
      step99o150_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 264 : Mat3).transpose = codeMat 258 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h1
    -- g=130, g^T=40; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 2 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 330) (codeMat 354) (codeMat 2) = codeMat 40 := by
      unfold actionA
      rw [step99o150s5_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 2 * (codeMat 142 : Mat3).transpose = codeMat 40
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 40 ∈ actionW (codeMat 330) (codeMat 354) o55W :=
      step99o150_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 40 : Mat3).transpose = codeMat 130 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h2
    -- g=68, g^T=68; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 272 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 272 (by decide)
    have hact : actionA (codeMat 330) (codeMat 354) (codeMat 272) = codeMat 68 := by
      unfold actionA
      rw [step99o150s5_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 272 * (codeMat 142 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 68 ∈ actionW (codeMat 330) (codeMat 354) o55W :=
      step99o150_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 68 : Mat3).transpose = codeMat 68 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h3
    -- g=16, g^T=16; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 1 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 330) (codeMat 354) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step99o150s5_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 1 * (codeMat 142 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 16 ∈ actionW (codeMat 330) (codeMat 354) o55W :=
      step99o150_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 16 : Mat3).transpose = codeMat 16 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h4
    -- g=10, g^T=10; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 12 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 12 (by decide)
    have hact : actionA (codeMat 330) (codeMat 354) (codeMat 12) = codeMat 10 := by
      unfold actionA
      rw [step99o150s5_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 12 * (codeMat 142 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 10 ∈ actionW (codeMat 330) (codeMat 354) o55W :=
      step99o150_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 10 : Mat3).transpose = codeMat 10 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h5
    -- g=1, g^T=1; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 32 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 330) (codeMat 354) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step99o150s5_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 32 * (codeMat 142 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 1 ∈ actionW (codeMat 330) (codeMat 354) o55W :=
      step99o150_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 1 : Mat3).transpose = codeMat 1 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_transposeW_of_witness hmemAction htrans

theorem step99o150s5Dispatch :
    QuotientRankAtLeast (o150SourceU ⟨5, by omega⟩) 14 := by
  have hP : Invertible (codeMat 330 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 354 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 330) (codeMat 354) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 330) (codeMat 354) hP hQ o55W 14 step99_orbit55_lb14_unconditional
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 330) (codeMat 354) o55W)) 14 :=
    quotientRankAtLeast_transpose hAct
  have hMono : QuotientRankAtLeast step99o150ActualSource5 14 :=
    quotientRankAtLeast_mono step99o150s5_targetSpan_le_transposeAction hT
  exact quotientRankAtLeast_mono step99o150s5_sourceU_le hMono

-- Source 6 (row 11): orbit 55, lb 14
def step99o150ActualSource6 : Submodule F2 Mat3 := spanCodes [258, 132, 68, 16, 10, 1]

private theorem step99o150s6_sourceU_le :
    (o150SourceU ⟨6, by omega⟩) ≤ step99o150ActualSource6 := by
  intro M hM
  have hbool : spanContainsCodeCore [258, 132, 68, 16, 10, 1] (step99o150MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 266) ⊓ kerEvalFunc (codeMat 128 + codeMat 68)) ⊓ kerEvalFunc (codeMat 32)) at hM
    change ((evalFunc (codeMat 266) M = 0 ∧ evalFunc (codeMat 128 + codeMat 68) M = 0) ∧ evalFunc (codeMat 32) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 132, 68, 16, 10, 1] (step99o150MatrixCodeNat M) hbool
  rwa [step99o150_codeMat_matrixCode] at hspan

private theorem step99o150s6_QtInv :
    (codeMat 226 : Mat3).transpose⁻¹ = (codeMat 141 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 226 : Mat3).transpose * (codeMat 141 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o150s6_targetSpan_le_transposeAction :
    step99o150ActualSource6 ≤ transposeW (actionW (codeMat 267) (codeMat 226) o55W) := by
  apply step99o150_spanCodes_le_of_gens [258, 132, 68, 16, 10, 1]
    (transposeW (actionW (codeMat 267) (codeMat 226) o55W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    -- g=258, g^T=264; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 164 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 164 (by decide)
    have hact : actionA (codeMat 267) (codeMat 226) (codeMat 164) = codeMat 264 := by
      unfold actionA
      rw [step99o150s6_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 164 * (codeMat 141 : Mat3).transpose = codeMat 264
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 264 ∈ actionW (codeMat 267) (codeMat 226) o55W :=
      step99o150_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 264 : Mat3).transpose = codeMat 258 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h1
    -- g=132, g^T=96; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 274 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 274 (by decide)
    have hact : actionA (codeMat 267) (codeMat 226) (codeMat 274) = codeMat 96 := by
      unfold actionA
      rw [step99o150s6_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 274 * (codeMat 141 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 96 ∈ actionW (codeMat 267) (codeMat 226) o55W :=
      step99o150_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 96 : Mat3).transpose = codeMat 132 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h2
    -- g=68, g^T=68; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 272 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 272 (by decide)
    have hact : actionA (codeMat 267) (codeMat 226) (codeMat 272) = codeMat 68 := by
      unfold actionA
      rw [step99o150s6_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 272 * (codeMat 141 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 68 ∈ actionW (codeMat 267) (codeMat 226) o55W :=
      step99o150_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 68 : Mat3).transpose = codeMat 68 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h3
    -- g=16, g^T=16; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 45 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 45 (by decide)
    have hact : actionA (codeMat 267) (codeMat 226) (codeMat 45) = codeMat 16 := by
      unfold actionA
      rw [step99o150s6_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 45 * (codeMat 141 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 16 ∈ actionW (codeMat 267) (codeMat 226) o55W :=
      step99o150_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 16 : Mat3).transpose = codeMat 16 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h4
    -- g=10, g^T=10; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 12 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 12 (by decide)
    have hact : actionA (codeMat 267) (codeMat 226) (codeMat 12) = codeMat 10 := by
      unfold actionA
      rw [step99o150s6_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 12 * (codeMat 141 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 10 ∈ actionW (codeMat 267) (codeMat 226) o55W :=
      step99o150_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 10 : Mat3).transpose = codeMat 10 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h5
    -- g=1, g^T=1; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 32 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 267) (codeMat 226) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step99o150s6_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 32 * (codeMat 141 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 1 ∈ actionW (codeMat 267) (codeMat 226) o55W :=
      step99o150_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 1 : Mat3).transpose = codeMat 1 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_transposeW_of_witness hmemAction htrans

theorem step99o150s6Dispatch :
    QuotientRankAtLeast (o150SourceU ⟨6, by omega⟩) 14 := by
  have hP : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 226 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 267) (codeMat 226) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 267) (codeMat 226) hP hQ o55W 14 step99_orbit55_lb14_unconditional
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 267) (codeMat 226) o55W)) 14 :=
    quotientRankAtLeast_transpose hAct
  have hMono : QuotientRankAtLeast step99o150ActualSource6 14 :=
    quotientRankAtLeast_mono step99o150s6_targetSpan_le_transposeAction hT
  exact quotientRankAtLeast_mono step99o150s6_sourceU_le hMono

-- Source 7 (row 13): orbit 30, lb 12
def step99o150ActualSource7 : Submodule F2 Mat3 := spanCodes [256, 68, 16, 8, 2, 1]

private theorem step99o150s7_sourceU_le :
    (o150SourceU ⟨7, by omega⟩) ≤ step99o150ActualSource7 := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 68, 16, 8, 2, 1] (step99o150MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 128) ⊓ kerEvalFunc (codeMat 68)) ⊓ kerEvalFunc (codeMat 32)) at hM
    change ((evalFunc (codeMat 128) M = 0 ∧ evalFunc (codeMat 68) M = 0) ∧ evalFunc (codeMat 32) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 68, 16, 8, 2, 1] (step99o150MatrixCodeNat M) hbool
  rwa [step99o150_codeMat_matrixCode] at hspan

private theorem step99o150s7_contain :
    step99o150ActualSource7 ≤ monoW_30 := by
  apply step99o150_spanCodes_le_of_gens [256, 68, 16, 8, 2, 1] monoW_30
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 68, 16, 8, 2, 1] 256 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 68, 16, 8, 2, 1] 68 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 68, 16, 8, 2, 1] 16 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 68, 16, 8, 2, 1] 8 (by decide)
  · subst h4
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 68, 16, 8, 2, 1] 2 (by decide)
  · subst h5
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 68, 16, 8, 2, 1] 1 (by decide)

theorem step99o150s7Dispatch :
    QuotientRankAtLeast (o150SourceU ⟨7, by omega⟩) 12 :=
  quotientRankAtLeast_mono (le_trans step99o150s7_sourceU_le step99o150s7_contain) step99_mono_30_lb12

-- Source 8 (row 52): orbit 3, lb 9
def step99o150ActualSource8 : Submodule F2 Mat3 := spanCodes [258, 128, 66, 32, 16, 10, 6, 1]

private theorem step99o150s8_sourceU_le :
    (o150SourceU ⟨8, by omega⟩) ≤ step99o150ActualSource8 := by
  intro M hM
  have hbool : spanContainsCodeCore [258, 128, 66, 32, 16, 10, 6, 1] (step99o150MatrixCodeNat M) = true := by
    change M ∈ kerEvalFunc (codeMat 266 + codeMat 68) at hM
    change evalFunc (codeMat 266 + codeMat 68) M = 0 at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 128, 66, 32, 16, 10, 6, 1] (step99o150MatrixCodeNat M) hbool
  rwa [step99o150_codeMat_matrixCode] at hspan

private theorem step99o150s8_QtInv :
    (codeMat 334 : Mat3).transpose⁻¹ = (codeMat 442 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 334 : Mat3).transpose * (codeMat 442 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o150s8_targetSpan_le_action :
    step99o150ActualSource8 ≤ actionW (codeMat 84) (codeMat 334) flatW_3 := by
  apply step99o150_spanCodes_le_of_gens [258, 128, 66, 32, 16, 10, 6, 1]
    (actionW (codeMat 84) (codeMat 334) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 69 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 69 (by decide)
    have hact : actionA (codeMat 84) (codeMat 334) (codeMat 69) = codeMat 258 := by
      unfold actionA
      rw [step99o150s8_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 69 * (codeMat 442 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 334) (codeMat 1) = codeMat 128 := by
      unfold actionA
      rw [step99o150s8_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 442 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 70 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 70 (by decide)
    have hact : actionA (codeMat 84) (codeMat 334) (codeMat 70) = codeMat 66 := by
      unfold actionA
      rw [step99o150s8_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 70 * (codeMat 442 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 40 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 84) (codeMat 334) (codeMat 40) = codeMat 32 := by
      unfold actionA
      rw [step99o150s8_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 40 * (codeMat 442 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 334) (codeMat 8) = codeMat 16 := by
      unfold actionA
      rw [step99o150s8_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 442 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 112 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 112 (by decide)
    have hact : actionA (codeMat 84) (codeMat 334) (codeMat 112) = codeMat 10 := by
      unfold actionA
      rw [step99o150s8_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 112 * (codeMat 442 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 334) (codeMat 256) = codeMat 6 := by
      unfold actionA
      rw [step99o150s8_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 442 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 334) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step99o150s8_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 442 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o150_codeMat_mem_actionW_of_witness hw hact

theorem step99o150s8Dispatch :
    QuotientRankAtLeast (o150SourceU ⟨8, by omega⟩) 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 334 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 334) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 334) hP hQ flatW_3 9 flatSeed_3
  have hMono : QuotientRankAtLeast step99o150ActualSource8 9 :=
    quotientRankAtLeast_mono step99o150s8_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o150s8_sourceU_le hMono

theorem step99o150_all_dispatch (i : Fin 9) :
    QuotientRankAtLeast (o150SourceU i) (o150SourceLb i) := by
  fin_cases i
  · exact step99o150s0Dispatch
  · exact step99o150s1Dispatch
  · exact step99o150s2Dispatch
  · exact step99o150s3Dispatch
  · exact step99o150s4Dispatch
  · exact step99o150s5Dispatch
  · exact step99o150s6Dispatch
  · exact step99o150s7Dispatch
  · exact step99o150s8Dispatch

theorem step99_orbit150_lb16_unconditional :
    QuotientRankAtLeast o150W 16 :=
  o150Lb16 step99o150_all_dispatch

end QiushiMatmul
