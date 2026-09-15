import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiFlattenSeeds
import QiushiStep108Orbit450Consumer
import QiushiStep104Orbit279Split
import QiushiStep107Orbit373Extraction
import QiushiStep99Orbit377Dispatch

set_option maxHeartbeats 800000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step108o450_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step108o450MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step108o450_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step108o450MatrixCodeNat M) = M := by decide

private theorem step108o450_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by intro M hM; rcases hM with ⟨n, hn, rfl⟩; exact h n hn)

private theorem step108o450_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

-- Source 0: orbit 279, lb 17
def step108o450ActualSource0 : Submodule F2 Mat3 := spanCodes [68, 18, 10, 1]

private theorem step108o450s0_sourceU_le :
    (o450SourceU ⟨0, by omega⟩) ≤ step108o450ActualSource0 := by
  intro M hM
  have hbool : spanContainsCodeCore [68, 18, 10, 1] (step108o450MatrixCodeNat M) = true := by
    change M ∈ ((((kerEvalFunc (codeMat 32) ⊓ kerEvalFunc (codeMat 128)) ⊓ kerEvalFunc (codeMat 256)) ⊓ kerEvalFunc (codeMat 68)) ⊓ kerEvalFunc (codeMat 17 + codeMat 11)) at hM
    change ((((evalFunc (codeMat 32) M = 0 ∧ evalFunc (codeMat 128) M = 0) ∧ evalFunc (codeMat 256) M = 0) ∧ evalFunc (codeMat 68) M = 0) ∧ evalFunc (codeMat 17 + codeMat 11) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [68, 18, 10, 1] (step108o450MatrixCodeNat M) hbool
  rwa [step108o450_codeMat_matrixCode_all] at hspan

private theorem step108o450s0_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = (codeMat 275 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * (codeMat 275 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step108o450s0_contain :
    step108o450ActualSource0 ≤ actionW (codeMat 273) (codeMat 275) o279W := by
  apply step108o450_spanCodes_le_of_gens [68, 18, 10, 1]
    (actionW (codeMat 273) (codeMat 275) o279W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    have hw : codeMat 68 ∈ o279W :=
      spanContainsCodeCore_implies_mem_spanCodes [68, 16, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 68) = codeMat 68 := by
      unfold actionA
      rw [step108o450s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 68 * (codeMat 275 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 27 ∈ o279W :=
      spanContainsCodeCore_implies_mem_spanCodes [68, 16, 10, 1] 27 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 27) = codeMat 18 := by
      unfold actionA
      rw [step108o450s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 27 * (codeMat 275 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 11 ∈ o279W :=
      spanContainsCodeCore_implies_mem_spanCodes [68, 16, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 11) = codeMat 10 := by
      unfold actionA
      rw [step108o450s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 11 * (codeMat 275 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o279W :=
      spanContainsCodeCore_implies_mem_spanCodes [68, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step108o450s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 275 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact

theorem step108o450s0Dispatch :
    QuotientRankAtLeast (o450SourceU ⟨0, by omega⟩) 17 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 275) o279W) 17 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 275) hP hQ o279W 17 step104_orbit279_lb17
  exact quotientRankAtLeast_mono (le_trans step108o450s0_sourceU_le step108o450s0_contain) hAct

-- Source 1: orbit 377, lb 17
def step108o450ActualSource1 : Submodule F2 Mat3 := spanCodes [161, 68, 19, 10]

private theorem step108o450s1_sourceU_le :
    (o450SourceU ⟨1, by omega⟩) ≤ step108o450ActualSource1 := by
  intro M hM
  have hbool : spanContainsCodeCore [161, 68, 19, 10] (step108o450MatrixCodeNat M) = true := by
    change M ∈ ((((kerEvalFunc (codeMat 256) ⊓ kerEvalFunc (codeMat 68)) ⊓ kerEvalFunc (codeMat 32 + codeMat 128)) ⊓ kerEvalFunc (codeMat 17 + codeMat 11)) ⊓ kerEvalFunc (codeMat 32 + codeMat 17)) at hM
    change ((((evalFunc (codeMat 256) M = 0 ∧ evalFunc (codeMat 68) M = 0) ∧ evalFunc (codeMat 32 + codeMat 128) M = 0) ∧ evalFunc (codeMat 17 + codeMat 11) M = 0) ∧ evalFunc (codeMat 32 + codeMat 17) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [161, 68, 19, 10] (step108o450MatrixCodeNat M) hbool
  rwa [step108o450_codeMat_matrixCode_all] at hspan

private theorem step108o450s1_QtInv :
    (codeMat 302 : Mat3).transpose⁻¹ = (codeMat 302 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 302 : Mat3).transpose * (codeMat 302 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step108o450s1_contain :
    step108o450ActualSource1 ≤ actionW (codeMat 266) (codeMat 302) o377W := by
  apply step108o450_spanCodes_le_of_gens [161, 68, 19, 10]
    (actionW (codeMat 266) (codeMat 302) o377W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    have hw : codeMat 87 ∈ o377W :=
      spanContainsCodeCore_implies_mem_spanCodes [161, 68, 19, 10] 87 (by decide)
    have hact : actionA (codeMat 266) (codeMat 302) (codeMat 87) = codeMat 161 := by
      unfold actionA
      rw [step108o450s1_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 87 * (codeMat 302 : Mat3).transpose = codeMat 161
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 184 ∈ o377W :=
      spanContainsCodeCore_implies_mem_spanCodes [161, 68, 19, 10] 184 (by decide)
    have hact : actionA (codeMat 266) (codeMat 302) (codeMat 184) = codeMat 68 := by
      unfold actionA
      rw [step108o450s1_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 184 * (codeMat 302 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 25 ∈ o377W :=
      spanContainsCodeCore_implies_mem_spanCodes [161, 68, 19, 10] 25 (by decide)
    have hact : actionA (codeMat 266) (codeMat 302) (codeMat 25) = codeMat 19 := by
      unfold actionA
      rw [step108o450s1_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 25 * (codeMat 302 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 10 ∈ o377W :=
      spanContainsCodeCore_implies_mem_spanCodes [161, 68, 19, 10] 10 (by decide)
    have hact : actionA (codeMat 266) (codeMat 302) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step108o450s1_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 10 * (codeMat 302 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact

theorem step108o450s1Dispatch :
    QuotientRankAtLeast (o450SourceU ⟨1, by omega⟩) 17 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 302 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 302) o377W) 17 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 302) hP hQ o377W 17 step99_orbit377_lb17_unconditional
  exact quotientRankAtLeast_mono (le_trans step108o450s1_sourceU_le step108o450s1_contain) hAct

-- Source 2: orbit 373, lb 17
def step108o450ActualSource2 : Submodule F2 Mat3 := spanCodes [288, 68, 19, 10]

private theorem step108o450s2_sourceU_le :
    (o450SourceU ⟨2, by omega⟩) ≤ step108o450ActualSource2 := by
  intro M hM
  have hbool : spanContainsCodeCore [288, 68, 19, 10] (step108o450MatrixCodeNat M) = true := by
    change M ∈ ((((kerEvalFunc (codeMat 128) ⊓ kerEvalFunc (codeMat 17)) ⊓ kerEvalFunc (codeMat 68)) ⊓ kerEvalFunc (codeMat 32 + codeMat 256)) ⊓ kerEvalFunc (codeMat 11)) at hM
    change ((((evalFunc (codeMat 128) M = 0 ∧ evalFunc (codeMat 17) M = 0) ∧ evalFunc (codeMat 68) M = 0) ∧ evalFunc (codeMat 32 + codeMat 256) M = 0) ∧ evalFunc (codeMat 11) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 68, 19, 10] (step108o450MatrixCodeNat M) hbool
  rwa [step108o450_codeMat_matrixCode_all] at hspan

private theorem step108o450s2_QtInv :
    (codeMat 86 : Mat3).transpose⁻¹ = (codeMat 212 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 86 : Mat3).transpose * (codeMat 212 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step108o450s2_contain :
    step108o450ActualSource2 ≤ actionW (codeMat 206) (codeMat 86) o373W := by
  apply step108o450_spanCodes_le_of_gens [288, 68, 19, 10]
    (actionW (codeMat 206) (codeMat 86) o373W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    have hw : codeMat 1 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 1 (by decide)
    have hact : actionA (codeMat 206) (codeMat 86) (codeMat 1) = codeMat 288 := by
      unfold actionA
      rw [step108o450s2_QtInv]
      show (codeMat 206 : Mat3).transpose * codeMat 1 * (codeMat 212 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 300 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 300 (by decide)
    have hact : actionA (codeMat 206) (codeMat 86) (codeMat 300) = codeMat 68 := by
      unfold actionA
      rw [step108o450s2_QtInv]
      show (codeMat 206 : Mat3).transpose * codeMat 300 * (codeMat 212 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 224 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 224 (by decide)
    have hact : actionA (codeMat 206) (codeMat 86) (codeMat 224) = codeMat 19 := by
      unfold actionA
      rw [step108o450s2_QtInv]
      show (codeMat 206 : Mat3).transpose * codeMat 224 * (codeMat 212 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 312 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 312 (by decide)
    have hact : actionA (codeMat 206) (codeMat 86) (codeMat 312) = codeMat 10 := by
      unfold actionA
      rw [step108o450s2_QtInv]
      show (codeMat 206 : Mat3).transpose * codeMat 312 * (codeMat 212 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact

theorem step108o450s2Dispatch :
    QuotientRankAtLeast (o450SourceU ⟨2, by omega⟩) 17 := by
  have hP : Invertible (codeMat 206 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 86 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 206) (codeMat 86) o373W) 17 :=
    @quotientRankAtLeast_action (codeMat 206) (codeMat 86) hP hQ o373W 17 step107_orbit373_lb17
  exact quotientRankAtLeast_mono (le_trans step108o450s2_sourceU_le step108o450s2_contain) hAct

-- Source 3: orbit 373, lb 17
def step108o450ActualSource3 : Submodule F2 Mat3 := spanCodes [291, 68, 19, 10]

private theorem step108o450s3_sourceU_le :
    (o450SourceU ⟨3, by omega⟩) ≤ step108o450ActualSource3 := by
  intro M hM
  have hbool : spanContainsCodeCore [291, 68, 19, 10] (step108o450MatrixCodeNat M) = true := by
    change M ∈ ((((kerEvalFunc (codeMat 128) ⊓ kerEvalFunc (codeMat 68)) ⊓ kerEvalFunc (codeMat 32 + codeMat 256)) ⊓ kerEvalFunc (codeMat 11)) ⊓ kerEvalFunc (codeMat 32 + codeMat 17)) at hM
    change ((((evalFunc (codeMat 128) M = 0 ∧ evalFunc (codeMat 68) M = 0) ∧ evalFunc (codeMat 32 + codeMat 256) M = 0) ∧ evalFunc (codeMat 11) M = 0) ∧ evalFunc (codeMat 32 + codeMat 17) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [291, 68, 19, 10] (step108o450MatrixCodeNat M) hbool
  rwa [step108o450_codeMat_matrixCode_all] at hspan

private theorem step108o450s3_QtInv :
    (codeMat 342 : Mat3).transpose⁻¹ = (codeMat 215 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 342 : Mat3).transpose * (codeMat 215 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step108o450s3_contain :
    step108o450ActualSource3 ≤ actionW (codeMat 207) (codeMat 342) o373W := by
  apply step108o450_spanCodes_le_of_gens [291, 68, 19, 10]
    (actionW (codeMat 207) (codeMat 342) o373W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    have hw : codeMat 21 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 21 (by decide)
    have hact : actionA (codeMat 207) (codeMat 342) (codeMat 21) = codeMat 291 := by
      unfold actionA
      rw [step108o450s3_QtInv]
      show (codeMat 207 : Mat3).transpose * codeMat 21 * (codeMat 215 : Mat3).transpose = codeMat 291
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 300 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 300 (by decide)
    have hact : actionA (codeMat 207) (codeMat 342) (codeMat 300) = codeMat 68 := by
      unfold actionA
      rw [step108o450s3_QtInv]
      show (codeMat 207 : Mat3).transpose * codeMat 300 * (codeMat 215 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 224 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 224 (by decide)
    have hact : actionA (codeMat 207) (codeMat 342) (codeMat 224) = codeMat 19 := by
      unfold actionA
      rw [step108o450s3_QtInv]
      show (codeMat 207 : Mat3).transpose * codeMat 224 * (codeMat 215 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 312 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 312 (by decide)
    have hact : actionA (codeMat 207) (codeMat 342) (codeMat 312) = codeMat 10 := by
      unfold actionA
      rw [step108o450s3_QtInv]
      show (codeMat 207 : Mat3).transpose * codeMat 312 * (codeMat 215 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact

theorem step108o450s3Dispatch :
    QuotientRankAtLeast (o450SourceU ⟨3, by omega⟩) 17 := by
  have hP : Invertible (codeMat 207 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 342 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 207) (codeMat 342) o373W) 17 :=
    @quotientRankAtLeast_action (codeMat 207) (codeMat 342) hP hQ o373W 17 step107_orbit373_lb17
  exact quotientRankAtLeast_mono (le_trans step108o450s3_sourceU_le step108o450s3_contain) hAct

-- Source 4: orbit 373, lb 17
def step108o450ActualSource4 : Submodule F2 Mat3 := spanCodes [292, 68, 19, 10]

private theorem step108o450s4_sourceU_le :
    (o450SourceU ⟨4, by omega⟩) ≤ step108o450ActualSource4 := by
  intro M hM
  have hbool : spanContainsCodeCore [292, 68, 19, 10] (step108o450MatrixCodeNat M) = true := by
    change M ∈ ((((kerEvalFunc (codeMat 128) ⊓ kerEvalFunc (codeMat 17)) ⊓ kerEvalFunc (codeMat 32 + codeMat 256)) ⊓ kerEvalFunc (codeMat 11)) ⊓ kerEvalFunc (codeMat 32 + codeMat 68)) at hM
    change ((((evalFunc (codeMat 128) M = 0 ∧ evalFunc (codeMat 17) M = 0) ∧ evalFunc (codeMat 32 + codeMat 256) M = 0) ∧ evalFunc (codeMat 11) M = 0) ∧ evalFunc (codeMat 32 + codeMat 68) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [292, 68, 19, 10] (step108o450MatrixCodeNat M) hbool
  rwa [step108o450_codeMat_matrixCode_all] at hspan

private theorem step108o450s4_QtInv :
    (codeMat 214 : Mat3).transpose⁻¹ = (codeMat 214 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 214 : Mat3).transpose * (codeMat 214 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step108o450s4_contain :
    step108o450ActualSource4 ≤ actionW (codeMat 143) (codeMat 214) o373W := by
  apply step108o450_spanCodes_le_of_gens [292, 68, 19, 10]
    (actionW (codeMat 143) (codeMat 214) o373W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    have hw : codeMat 1 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 1 (by decide)
    have hact : actionA (codeMat 143) (codeMat 214) (codeMat 1) = codeMat 292 := by
      unfold actionA
      rw [step108o450s4_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 1 * (codeMat 214 : Mat3).transpose = codeMat 292
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 300 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 300 (by decide)
    have hact : actionA (codeMat 143) (codeMat 214) (codeMat 300) = codeMat 68 := by
      unfold actionA
      rw [step108o450s4_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 300 * (codeMat 214 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 472 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 472 (by decide)
    have hact : actionA (codeMat 143) (codeMat 214) (codeMat 472) = codeMat 19 := by
      unfold actionA
      rw [step108o450s4_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 472 * (codeMat 214 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 312 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 312 (by decide)
    have hact : actionA (codeMat 143) (codeMat 214) (codeMat 312) = codeMat 10 := by
      unfold actionA
      rw [step108o450s4_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 312 * (codeMat 214 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact

theorem step108o450s4Dispatch :
    QuotientRankAtLeast (o450SourceU ⟨4, by omega⟩) 17 := by
  have hP : Invertible (codeMat 143 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 214 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 143) (codeMat 214) o373W) 17 :=
    @quotientRankAtLeast_action (codeMat 143) (codeMat 214) hP hQ o373W 17 step107_orbit373_lb17
  exact quotientRankAtLeast_mono (le_trans step108o450s4_sourceU_le step108o450s4_contain) hAct

-- Source 5: orbit 373, lb 17
def step108o450ActualSource5 : Submodule F2 Mat3 := spanCodes [294, 68, 19, 10]

private theorem step108o450s5_sourceU_le :
    (o450SourceU ⟨5, by omega⟩) ≤ step108o450ActualSource5 := by
  intro M hM
  have hbool : spanContainsCodeCore [294, 68, 19, 10] (step108o450MatrixCodeNat M) = true := by
    change M ∈ ((((kerEvalFunc (codeMat 128) ⊓ kerEvalFunc (codeMat 17)) ⊓ kerEvalFunc (codeMat 32 + codeMat 256)) ⊓ kerEvalFunc (codeMat 32 + codeMat 68)) ⊓ kerEvalFunc (codeMat 32 + codeMat 11)) at hM
    change ((((evalFunc (codeMat 128) M = 0 ∧ evalFunc (codeMat 17) M = 0) ∧ evalFunc (codeMat 32 + codeMat 256) M = 0) ∧ evalFunc (codeMat 32 + codeMat 68) M = 0) ∧ evalFunc (codeMat 32 + codeMat 11) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [294, 68, 19, 10] (step108o450MatrixCodeNat M) hbool
  rwa [step108o450_codeMat_matrixCode_all] at hspan

private theorem step108o450s5_QtInv :
    (codeMat 470 : Mat3).transpose⁻¹ = (codeMat 213 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 470 : Mat3).transpose * (codeMat 213 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step108o450s5_contain :
    step108o450ActualSource5 ≤ actionW (codeMat 142) (codeMat 470) o373W := by
  apply step108o450_spanCodes_le_of_gens [294, 68, 19, 10]
    (actionW (codeMat 142) (codeMat 470) o373W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    have hw : codeMat 21 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 21 (by decide)
    have hact : actionA (codeMat 142) (codeMat 470) (codeMat 21) = codeMat 294 := by
      unfold actionA
      rw [step108o450s5_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 21 * (codeMat 213 : Mat3).transpose = codeMat 294
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 300 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 300 (by decide)
    have hact : actionA (codeMat 142) (codeMat 470) (codeMat 300) = codeMat 68 := by
      unfold actionA
      rw [step108o450s5_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 300 * (codeMat 213 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 472 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 472 (by decide)
    have hact : actionA (codeMat 142) (codeMat 470) (codeMat 472) = codeMat 19 := by
      unfold actionA
      rw [step108o450s5_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 472 * (codeMat 213 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 312 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 312 (by decide)
    have hact : actionA (codeMat 142) (codeMat 470) (codeMat 312) = codeMat 10 := by
      unfold actionA
      rw [step108o450s5_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 312 * (codeMat 213 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact

theorem step108o450s5Dispatch :
    QuotientRankAtLeast (o450SourceU ⟨5, by omega⟩) 17 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 470 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 470) o373W) 17 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 470) hP hQ o373W 17 step107_orbit373_lb17
  exact quotientRankAtLeast_mono (le_trans step108o450s5_sourceU_le step108o450s5_contain) hAct

-- Source 6: orbit 373, lb 17
def step108o450ActualSource6 : Submodule F2 Mat3 := spanCodes [384, 68, 19, 10]

private theorem step108o450s6_sourceU_le :
    (o450SourceU ⟨6, by omega⟩) ≤ step108o450ActualSource6 := by
  intro M hM
  have hbool : spanContainsCodeCore [384, 68, 19, 10] (step108o450MatrixCodeNat M) = true := by
    change M ∈ ((((kerEvalFunc (codeMat 32) ⊓ kerEvalFunc (codeMat 17)) ⊓ kerEvalFunc (codeMat 68)) ⊓ kerEvalFunc (codeMat 128 + codeMat 256)) ⊓ kerEvalFunc (codeMat 11)) at hM
    change ((((evalFunc (codeMat 32) M = 0 ∧ evalFunc (codeMat 17) M = 0) ∧ evalFunc (codeMat 68) M = 0) ∧ evalFunc (codeMat 128 + codeMat 256) M = 0) ∧ evalFunc (codeMat 11) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [384, 68, 19, 10] (step108o450MatrixCodeNat M) hbool
  rwa [step108o450_codeMat_matrixCode_all] at hspan

private theorem step108o450s6_QtInv :
    (codeMat 114 : Mat3).transpose⁻¹ = (codeMat 204 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 114 : Mat3).transpose * (codeMat 204 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step108o450s6_contain :
    step108o450ActualSource6 ≤ actionW (codeMat 204) (codeMat 114) o373W := by
  apply step108o450_spanCodes_le_of_gens [384, 68, 19, 10]
    (actionW (codeMat 204) (codeMat 114) o373W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    have hw : codeMat 1 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 1 (by decide)
    have hact : actionA (codeMat 204) (codeMat 114) (codeMat 1) = codeMat 384 := by
      unfold actionA
      rw [step108o450s6_QtInv]
      show (codeMat 204 : Mat3).transpose * codeMat 1 * (codeMat 204 : Mat3).transpose = codeMat 384
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 20 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 20 (by decide)
    have hact : actionA (codeMat 204) (codeMat 114) (codeMat 20) = codeMat 68 := by
      unfold actionA
      rw [step108o450s6_QtInv]
      show (codeMat 204 : Mat3).transpose * codeMat 20 * (codeMat 204 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 224 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 224 (by decide)
    have hact : actionA (codeMat 204) (codeMat 114) (codeMat 224) = codeMat 19 := by
      unfold actionA
      rw [step108o450s6_QtInv]
      show (codeMat 204 : Mat3).transpose * codeMat 224 * (codeMat 204 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 312 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 312 (by decide)
    have hact : actionA (codeMat 204) (codeMat 114) (codeMat 312) = codeMat 10 := by
      unfold actionA
      rw [step108o450s6_QtInv]
      show (codeMat 204 : Mat3).transpose * codeMat 312 * (codeMat 204 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact

theorem step108o450s6Dispatch :
    QuotientRankAtLeast (o450SourceU ⟨6, by omega⟩) 17 := by
  have hP : Invertible (codeMat 204 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 114 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 204) (codeMat 114) o373W) 17 :=
    @quotientRankAtLeast_action (codeMat 204) (codeMat 114) hP hQ o373W 17 step107_orbit373_lb17
  exact quotientRankAtLeast_mono (le_trans step108o450s6_sourceU_le step108o450s6_contain) hAct

-- Source 7: orbit 373, lb 17
def step108o450ActualSource7 : Submodule F2 Mat3 := spanCodes [387, 68, 19, 10]

private theorem step108o450s7_sourceU_le :
    (o450SourceU ⟨7, by omega⟩) ≤ step108o450ActualSource7 := by
  intro M hM
  have hbool : spanContainsCodeCore [387, 68, 19, 10] (step108o450MatrixCodeNat M) = true := by
    change M ∈ ((((kerEvalFunc (codeMat 32) ⊓ kerEvalFunc (codeMat 68)) ⊓ kerEvalFunc (codeMat 128 + codeMat 256)) ⊓ kerEvalFunc (codeMat 11)) ⊓ kerEvalFunc (codeMat 128 + codeMat 17)) at hM
    change ((((evalFunc (codeMat 32) M = 0 ∧ evalFunc (codeMat 68) M = 0) ∧ evalFunc (codeMat 128 + codeMat 256) M = 0) ∧ evalFunc (codeMat 11) M = 0) ∧ evalFunc (codeMat 128 + codeMat 17) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [387, 68, 19, 10] (step108o450MatrixCodeNat M) hbool
  rwa [step108o450_codeMat_matrixCode_all] at hspan

private theorem step108o450s7_QtInv :
    (codeMat 370 : Mat3).transpose⁻¹ = (codeMat 207 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 370 : Mat3).transpose * (codeMat 207 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step108o450s7_contain :
    step108o450ActualSource7 ≤ actionW (codeMat 205) (codeMat 370) o373W := by
  apply step108o450_spanCodes_le_of_gens [387, 68, 19, 10]
    (actionW (codeMat 205) (codeMat 370) o373W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    have hw : codeMat 21 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 21 (by decide)
    have hact : actionA (codeMat 205) (codeMat 370) (codeMat 21) = codeMat 387 := by
      unfold actionA
      rw [step108o450s7_QtInv]
      show (codeMat 205 : Mat3).transpose * codeMat 21 * (codeMat 207 : Mat3).transpose = codeMat 387
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 20 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 20 (by decide)
    have hact : actionA (codeMat 205) (codeMat 370) (codeMat 20) = codeMat 68 := by
      unfold actionA
      rw [step108o450s7_QtInv]
      show (codeMat 205 : Mat3).transpose * codeMat 20 * (codeMat 207 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 224 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 224 (by decide)
    have hact : actionA (codeMat 205) (codeMat 370) (codeMat 224) = codeMat 19 := by
      unfold actionA
      rw [step108o450s7_QtInv]
      show (codeMat 205 : Mat3).transpose * codeMat 224 * (codeMat 207 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 312 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 312 (by decide)
    have hact : actionA (codeMat 205) (codeMat 370) (codeMat 312) = codeMat 10 := by
      unfold actionA
      rw [step108o450s7_QtInv]
      show (codeMat 205 : Mat3).transpose * codeMat 312 * (codeMat 207 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact

theorem step108o450s7Dispatch :
    QuotientRankAtLeast (o450SourceU ⟨7, by omega⟩) 17 := by
  have hP : Invertible (codeMat 205 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 370 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 205) (codeMat 370) o373W) 17 :=
    @quotientRankAtLeast_action (codeMat 205) (codeMat 370) hP hQ o373W 17 step107_orbit373_lb17
  exact quotientRankAtLeast_mono (le_trans step108o450s7_sourceU_le step108o450s7_contain) hAct

-- Source 8: orbit 373, lb 17
def step108o450ActualSource8 : Submodule F2 Mat3 := spanCodes [388, 68, 19, 10]

private theorem step108o450s8_sourceU_le :
    (o450SourceU ⟨8, by omega⟩) ≤ step108o450ActualSource8 := by
  intro M hM
  have hbool : spanContainsCodeCore [388, 68, 19, 10] (step108o450MatrixCodeNat M) = true := by
    change M ∈ ((((kerEvalFunc (codeMat 32) ⊓ kerEvalFunc (codeMat 17)) ⊓ kerEvalFunc (codeMat 128 + codeMat 256)) ⊓ kerEvalFunc (codeMat 11)) ⊓ kerEvalFunc (codeMat 128 + codeMat 68)) at hM
    change ((((evalFunc (codeMat 32) M = 0 ∧ evalFunc (codeMat 17) M = 0) ∧ evalFunc (codeMat 128 + codeMat 256) M = 0) ∧ evalFunc (codeMat 11) M = 0) ∧ evalFunc (codeMat 128 + codeMat 68) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [388, 68, 19, 10] (step108o450MatrixCodeNat M) hbool
  rwa [step108o450_codeMat_matrixCode_all] at hspan

private theorem step108o450s8_QtInv :
    (codeMat 242 : Mat3).transpose⁻¹ = (codeMat 205 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 242 : Mat3).transpose * (codeMat 205 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step108o450s8_contain :
    step108o450ActualSource8 ≤ actionW (codeMat 140) (codeMat 242) o373W := by
  apply step108o450_spanCodes_le_of_gens [388, 68, 19, 10]
    (actionW (codeMat 140) (codeMat 242) o373W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    have hw : codeMat 21 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 21 (by decide)
    have hact : actionA (codeMat 140) (codeMat 242) (codeMat 21) = codeMat 388 := by
      unfold actionA
      rw [step108o450s8_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 21 * (codeMat 205 : Mat3).transpose = codeMat 388
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 20 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 20 (by decide)
    have hact : actionA (codeMat 140) (codeMat 242) (codeMat 20) = codeMat 68 := by
      unfold actionA
      rw [step108o450s8_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 20 * (codeMat 205 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 472 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 472 (by decide)
    have hact : actionA (codeMat 140) (codeMat 242) (codeMat 472) = codeMat 19 := by
      unfold actionA
      rw [step108o450s8_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 472 * (codeMat 205 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 312 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 312 (by decide)
    have hact : actionA (codeMat 140) (codeMat 242) (codeMat 312) = codeMat 10 := by
      unfold actionA
      rw [step108o450s8_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 312 * (codeMat 205 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact

theorem step108o450s8Dispatch :
    QuotientRankAtLeast (o450SourceU ⟨8, by omega⟩) 17 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 242 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 242) o373W) 17 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 242) hP hQ o373W 17 step107_orbit373_lb17
  exact quotientRankAtLeast_mono (le_trans step108o450s8_sourceU_le step108o450s8_contain) hAct

-- Source 9: orbit 373, lb 17
def step108o450ActualSource9 : Submodule F2 Mat3 := spanCodes [390, 68, 19, 10]

private theorem step108o450s9_sourceU_le :
    (o450SourceU ⟨9, by omega⟩) ≤ step108o450ActualSource9 := by
  intro M hM
  have hbool : spanContainsCodeCore [390, 68, 19, 10] (step108o450MatrixCodeNat M) = true := by
    change M ∈ ((((kerEvalFunc (codeMat 32) ⊓ kerEvalFunc (codeMat 17)) ⊓ kerEvalFunc (codeMat 128 + codeMat 256)) ⊓ kerEvalFunc (codeMat 128 + codeMat 68)) ⊓ kerEvalFunc (codeMat 128 + codeMat 11)) at hM
    change ((((evalFunc (codeMat 32) M = 0 ∧ evalFunc (codeMat 17) M = 0) ∧ evalFunc (codeMat 128 + codeMat 256) M = 0) ∧ evalFunc (codeMat 128 + codeMat 68) M = 0) ∧ evalFunc (codeMat 128 + codeMat 11) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [390, 68, 19, 10] (step108o450MatrixCodeNat M) hbool
  rwa [step108o450_codeMat_matrixCode_all] at hspan

private theorem step108o450s9_QtInv :
    (codeMat 498 : Mat3).transpose⁻¹ = (codeMat 206 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 498 : Mat3).transpose * (codeMat 206 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step108o450s9_contain :
    step108o450ActualSource9 ≤ actionW (codeMat 141) (codeMat 498) o373W := by
  apply step108o450_spanCodes_le_of_gens [390, 68, 19, 10]
    (actionW (codeMat 141) (codeMat 498) o373W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    have hw : codeMat 1 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 1 (by decide)
    have hact : actionA (codeMat 141) (codeMat 498) (codeMat 1) = codeMat 390 := by
      unfold actionA
      rw [step108o450s9_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 1 * (codeMat 206 : Mat3).transpose = codeMat 390
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 20 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 20 (by decide)
    have hact : actionA (codeMat 141) (codeMat 498) (codeMat 20) = codeMat 68 := by
      unfold actionA
      rw [step108o450s9_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 20 * (codeMat 206 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 472 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 472 (by decide)
    have hact : actionA (codeMat 141) (codeMat 498) (codeMat 472) = codeMat 19 := by
      unfold actionA
      rw [step108o450s9_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 472 * (codeMat 206 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 312 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 312 (by decide)
    have hact : actionA (codeMat 141) (codeMat 498) (codeMat 312) = codeMat 10 := by
      unfold actionA
      rw [step108o450s9_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 312 * (codeMat 206 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact

theorem step108o450s9Dispatch :
    QuotientRankAtLeast (o450SourceU ⟨9, by omega⟩) 17 := by
  have hP : Invertible (codeMat 141 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 498 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 141) (codeMat 498) o373W) 17 :=
    @quotientRankAtLeast_action (codeMat 141) (codeMat 498) hP hQ o373W 17 step107_orbit373_lb17
  exact quotientRankAtLeast_mono (le_trans step108o450s9_sourceU_le step108o450s9_contain) hAct

-- Source 10: orbit 3, lb 9
def step108o450ActualSource10 : Submodule F2 Mat3 := spanCodes [256, 129, 64, 33, 17, 8, 4, 2]

private theorem step108o450s10_sourceU_le :
    (o450SourceU ⟨10, by omega⟩) ≤ step108o450ActualSource10 := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 129, 64, 33, 17, 8, 4, 2] (step108o450MatrixCodeNat M) = true := by
    change M ∈ kerEvalFunc (codeMat 32 + codeMat 128 + codeMat 17) at hM
    change evalFunc (codeMat 32 + codeMat 128 + codeMat 17) M = 0 at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 129, 64, 33, 17, 8, 4, 2] (step108o450MatrixCodeNat M) hbool
  rwa [step108o450_codeMat_matrixCode_all] at hspan

private theorem step108o450s10_QtInv :
    (codeMat 177 : Mat3).transpose⁻¹ = (codeMat 417 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 177 : Mat3).transpose * (codeMat 417 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step108o450s10_contain :
    step108o450ActualSource10 ≤ actionW (codeMat 84) (codeMat 177) flatW_3 := by
  apply step108o450_spanCodes_le_of_gens [256, 129, 64, 33, 17, 8, 4, 2]
    (actionW (codeMat 84) (codeMat 177) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 2 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 177) (codeMat 2) = codeMat 256 := by
      unfold actionA
      rw [step108o450s10_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 417 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 70 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 70 (by decide)
    have hact : actionA (codeMat 84) (codeMat 177) (codeMat 70) = codeMat 129 := by
      unfold actionA
      rw [step108o450s10_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 70 * (codeMat 417 : Mat3).transpose = codeMat 129
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 177) (codeMat 1) = codeMat 64 := by
      unfold actionA
      rw [step108o450s10_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 417 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 80 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 80 (by decide)
    have hact : actionA (codeMat 84) (codeMat 177) (codeMat 80) = codeMat 33 := by
      unfold actionA
      rw [step108o450s10_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 80 * (codeMat 417 : Mat3).transpose = codeMat 33
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 112 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 112 (by decide)
    have hact : actionA (codeMat 84) (codeMat 177) (codeMat 112) = codeMat 17 := by
      unfold actionA
      rw [step108o450s10_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 112 * (codeMat 417 : Mat3).transpose = codeMat 17
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 177) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step108o450s10_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 417 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 177) (codeMat 128) = codeMat 4 := by
      unfold actionA
      rw [step108o450s10_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 417 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 177) (codeMat 384) = codeMat 2 := by
      unfold actionA
      rw [step108o450s10_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 417 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact

theorem step108o450s10Dispatch :
    QuotientRankAtLeast (o450SourceU ⟨10, by omega⟩) 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 177) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 177) hP hQ flatW_3 9 flatSeed_3
  exact quotientRankAtLeast_mono (le_trans step108o450s10_sourceU_le step108o450s10_contain) hAct

-- Source 11: orbit 3, lb 9
def step108o450ActualSource11 : Submodule F2 Mat3 := spanCodes [257, 129, 65, 33, 17, 8, 5, 2]

private theorem step108o450s11_sourceU_le :
    (o450SourceU ⟨11, by omega⟩) ≤ step108o450ActualSource11 := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 129, 65, 33, 17, 8, 5, 2] (step108o450MatrixCodeNat M) = true := by
    change M ∈ kerEvalFunc (codeMat 32 + codeMat 128 + codeMat 256 + codeMat 17 + codeMat 68) at hM
    change evalFunc (codeMat 32 + codeMat 128 + codeMat 256 + codeMat 17 + codeMat 68) M = 0 at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 129, 65, 33, 17, 8, 5, 2] (step108o450MatrixCodeNat M) hbool
  rwa [step108o450_codeMat_matrixCode_all] at hspan

private theorem step108o450s11_QtInv :
    (codeMat 501 : Mat3).transpose⁻¹ = (codeMat 494 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 501 : Mat3).transpose * (codeMat 494 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step108o450s11_contain :
    step108o450ActualSource11 ≤ actionW (codeMat 84) (codeMat 501) flatW_3 := by
  apply step108o450_spanCodes_le_of_gens [257, 129, 65, 33, 17, 8, 5, 2]
    (actionW (codeMat 84) (codeMat 501) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 327 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 327 (by decide)
    have hact : actionA (codeMat 84) (codeMat 501) (codeMat 327) = codeMat 257 := by
      unfold actionA
      rw [step108o450s11_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 327 * (codeMat 494 : Mat3).transpose = codeMat 257
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 326 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 326 (by decide)
    have hact : actionA (codeMat 84) (codeMat 501) (codeMat 326) = codeMat 129 := by
      unfold actionA
      rw [step108o450s11_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 326 * (codeMat 494 : Mat3).transpose = codeMat 129
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 325 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 325 (by decide)
    have hact : actionA (codeMat 84) (codeMat 501) (codeMat 325) = codeMat 65 := by
      unfold actionA
      rw [step108o450s11_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 325 * (codeMat 494 : Mat3).transpose = codeMat 65
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 376 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 376 (by decide)
    have hact : actionA (codeMat 84) (codeMat 501) (codeMat 376) = codeMat 33 := by
      unfold actionA
      rw [step108o450s11_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 376 * (codeMat 494 : Mat3).transpose = codeMat 33
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 368 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 368 (by decide)
    have hact : actionA (codeMat 84) (codeMat 501) (codeMat 368) = codeMat 17 := by
      unfold actionA
      rw [step108o450s11_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 368 * (codeMat 494 : Mat3).transpose = codeMat 17
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 40 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 84) (codeMat 501) (codeMat 40) = codeMat 8 := by
      unfold actionA
      rw [step108o450s11_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 40 * (codeMat 494 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 501) (codeMat 128) = codeMat 5 := by
      unfold actionA
      rw [step108o450s11_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 494 : Mat3).transpose = codeMat 5
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 501) (codeMat 384) = codeMat 2 := by
      unfold actionA
      rw [step108o450s11_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 494 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact

theorem step108o450s11Dispatch :
    QuotientRankAtLeast (o450SourceU ⟨11, by omega⟩) 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 501 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 501) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 501) hP hQ flatW_3 9 flatSeed_3
  exact quotientRankAtLeast_mono (le_trans step108o450s11_sourceU_le step108o450s11_contain) hAct

-- Source 12: orbit 3, lb 9
def step108o450ActualSource12 : Submodule F2 Mat3 := spanCodes [257, 128, 64, 32, 16, 9, 4, 3]

private theorem step108o450s12_sourceU_le :
    (o450SourceU ⟨12, by omega⟩) ≤ step108o450ActualSource12 := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 128, 64, 32, 16, 9, 4, 3] (step108o450MatrixCodeNat M) = true := by
    change M ∈ kerEvalFunc (codeMat 256 + codeMat 11) at hM
    change evalFunc (codeMat 256 + codeMat 11) M = 0 at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 128, 64, 32, 16, 9, 4, 3] (step108o450MatrixCodeNat M) hbool
  rwa [step108o450_codeMat_matrixCode_all] at hspan

private theorem step108o450s12_QtInv :
    (codeMat 267 : Mat3).transpose⁻¹ = (codeMat 282 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 267 : Mat3).transpose * (codeMat 282 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step108o450s12_contain :
    step108o450ActualSource12 ≤ actionW (codeMat 84) (codeMat 267) flatW_3 := by
  apply step108o450_spanCodes_le_of_gens [257, 128, 64, 32, 16, 9, 4, 3]
    (actionW (codeMat 84) (codeMat 267) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 196 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 196 (by decide)
    have hact : actionA (codeMat 84) (codeMat 267) (codeMat 196) = codeMat 257 := by
      unfold actionA
      rw [step108o450s12_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 196 * (codeMat 282 : Mat3).transpose = codeMat 257
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 267) (codeMat 1) = codeMat 128 := by
      unfold actionA
      rw [step108o450s12_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 282 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 3 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 84) (codeMat 267) (codeMat 3) = codeMat 64 := by
      unfold actionA
      rw [step108o450s12_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 3 * (codeMat 282 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 32 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 84) (codeMat 267) (codeMat 32) = codeMat 32 := by
      unfold actionA
      rw [step108o450s12_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 32 * (codeMat 282 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 267) (codeMat 8) = codeMat 16 := by
      unfold actionA
      rw [step108o450s12_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 282 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 216 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 216 (by decide)
    have hact : actionA (codeMat 84) (codeMat 267) (codeMat 216) = codeMat 9 := by
      unfold actionA
      rw [step108o450s12_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 216 * (codeMat 282 : Mat3).transpose = codeMat 9
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 267) (codeMat 256) = codeMat 4 := by
      unfold actionA
      rw [step108o450s12_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 282 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 128 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 267) (codeMat 128) = codeMat 3 := by
      unfold actionA
      rw [step108o450s12_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 282 : Mat3).transpose = codeMat 3
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact

theorem step108o450s12Dispatch :
    QuotientRankAtLeast (o450SourceU ⟨12, by omega⟩) 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 267) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 267) hP hQ flatW_3 9 flatSeed_3
  exact quotientRankAtLeast_mono (le_trans step108o450s12_sourceU_le step108o450s12_contain) hAct

-- Source 13: orbit 3, lb 9
def step108o450ActualSource13 : Submodule F2 Mat3 := spanCodes [256, 129, 65, 33, 16, 9, 5, 3]

private theorem step108o450s13_sourceU_le :
    (o450SourceU ⟨13, by omega⟩) ≤ step108o450ActualSource13 := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 129, 65, 33, 16, 9, 5, 3] (step108o450MatrixCodeNat M) = true := by
    change M ∈ kerEvalFunc (codeMat 32 + codeMat 128 + codeMat 68 + codeMat 11) at hM
    change evalFunc (codeMat 32 + codeMat 128 + codeMat 68 + codeMat 11) M = 0 at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 129, 65, 33, 16, 9, 5, 3] (step108o450MatrixCodeNat M) hbool
  rwa [step108o450_codeMat_matrixCode_all] at hspan

private theorem step108o450s13_QtInv :
    (codeMat 239 : Mat3).transpose⁻¹ = (codeMat 351 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 239 : Mat3).transpose * (codeMat 351 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step108o450s13_contain :
    step108o450ActualSource13 ≤ actionW (codeMat 84) (codeMat 239) flatW_3 := by
  apply step108o450_spanCodes_le_of_gens [256, 129, 65, 33, 16, 9, 5, 3]
    (actionW (codeMat 84) (codeMat 239) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 3 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 84) (codeMat 239) (codeMat 3) = codeMat 256 := by
      unfold actionA
      rw [step108o450s13_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 3 * (codeMat 351 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 453 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 453 (by decide)
    have hact : actionA (codeMat 84) (codeMat 239) (codeMat 453) = codeMat 129 := by
      unfold actionA
      rw [step108o450s13_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 453 * (codeMat 351 : Mat3).transpose = codeMat 129
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 455 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 455 (by decide)
    have hact : actionA (codeMat 84) (codeMat 239) (codeMat 455) = codeMat 65 := by
      unfold actionA
      rw [step108o450s13_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 455 * (codeMat 351 : Mat3).transpose = codeMat 65
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 472 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 472 (by decide)
    have hact : actionA (codeMat 84) (codeMat 239) (codeMat 472) = codeMat 33 := by
      unfold actionA
      rw [step108o450s13_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 472 * (codeMat 351 : Mat3).transpose = codeMat 33
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 40 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 84) (codeMat 239) (codeMat 40) = codeMat 16 := by
      unfold actionA
      rw [step108o450s13_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 40 * (codeMat 351 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 504 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 504 (by decide)
    have hact : actionA (codeMat 84) (codeMat 239) (codeMat 504) = codeMat 9 := by
      unfold actionA
      rw [step108o450s13_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 504 * (codeMat 351 : Mat3).transpose = codeMat 9
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 239) (codeMat 256) = codeMat 5 := by
      unfold actionA
      rw [step108o450s13_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 351 : Mat3).transpose = codeMat 5
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 128 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 239) (codeMat 128) = codeMat 3 := by
      unfold actionA
      rw [step108o450s13_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 351 : Mat3).transpose = codeMat 3
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact

theorem step108o450s13Dispatch :
    QuotientRankAtLeast (o450SourceU ⟨13, by omega⟩) 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 239 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 239) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 239) hP hQ flatW_3 9 flatSeed_3
  exact quotientRankAtLeast_mono (le_trans step108o450s13_sourceU_le step108o450s13_contain) hAct

-- Source 14: orbit 3, lb 9
def step108o450ActualSource14 : Submodule F2 Mat3 := spanCodes [257, 128, 65, 32, 16, 9, 5, 3]

private theorem step108o450s14_sourceU_le :
    (o450SourceU ⟨14, by omega⟩) ≤ step108o450ActualSource14 := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 128, 65, 32, 16, 9, 5, 3] (step108o450MatrixCodeNat M) = true := by
    change M ∈ kerEvalFunc (codeMat 256 + codeMat 68 + codeMat 11) at hM
    change evalFunc (codeMat 256 + codeMat 68 + codeMat 11) M = 0 at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 128, 65, 32, 16, 9, 5, 3] (step108o450MatrixCodeNat M) hbool
  rwa [step108o450_codeMat_matrixCode_all] at hspan

private theorem step108o450s14_QtInv :
    (codeMat 335 : Mat3).transpose⁻¹ = (codeMat 426 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 335 : Mat3).transpose * (codeMat 426 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step108o450s14_contain :
    step108o450ActualSource14 ≤ actionW (codeMat 84) (codeMat 335) flatW_3 := by
  apply step108o450_spanCodes_le_of_gens [257, 128, 65, 32, 16, 9, 5, 3]
    (actionW (codeMat 84) (codeMat 335) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 453 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 453 (by decide)
    have hact : actionA (codeMat 84) (codeMat 335) (codeMat 453) = codeMat 257 := by
      unfold actionA
      rw [step108o450s14_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 453 * (codeMat 426 : Mat3).transpose = codeMat 257
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 335) (codeMat 1) = codeMat 128 := by
      unfold actionA
      rw [step108o450s14_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 426 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 455 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 455 (by decide)
    have hact : actionA (codeMat 84) (codeMat 335) (codeMat 455) = codeMat 65 := by
      unfold actionA
      rw [step108o450s14_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 455 * (codeMat 426 : Mat3).transpose = codeMat 65
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 40 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 84) (codeMat 335) (codeMat 40) = codeMat 32 := by
      unfold actionA
      rw [step108o450s14_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 40 * (codeMat 426 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 335) (codeMat 8) = codeMat 16 := by
      unfold actionA
      rw [step108o450s14_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 426 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 504 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 504 (by decide)
    have hact : actionA (codeMat 84) (codeMat 335) (codeMat 504) = codeMat 9 := by
      unfold actionA
      rw [step108o450s14_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 504 * (codeMat 426 : Mat3).transpose = codeMat 9
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 335) (codeMat 128) = codeMat 5 := by
      unfold actionA
      rw [step108o450s14_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 426 : Mat3).transpose = codeMat 5
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 335) (codeMat 384) = codeMat 3 := by
      unfold actionA
      rw [step108o450s14_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 426 : Mat3).transpose = codeMat 3
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact

theorem step108o450s14Dispatch :
    QuotientRankAtLeast (o450SourceU ⟨14, by omega⟩) 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 335 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 335) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 335) hP hQ flatW_3 9 flatSeed_3
  exact quotientRankAtLeast_mono (le_trans step108o450s14_sourceU_le step108o450s14_contain) hAct

-- Source 15: orbit 3, lb 9
def step108o450ActualSource15 : Submodule F2 Mat3 := spanCodes [256, 129, 64, 33, 16, 9, 4, 3]

private theorem step108o450s15_sourceU_le :
    (o450SourceU ⟨15, by omega⟩) ≤ step108o450ActualSource15 := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 129, 64, 33, 16, 9, 4, 3] (step108o450MatrixCodeNat M) = true := by
    change M ∈ kerEvalFunc (codeMat 32 + codeMat 128 + codeMat 11) at hM
    change evalFunc (codeMat 32 + codeMat 128 + codeMat 11) M = 0 at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 129, 64, 33, 16, 9, 4, 3] (step108o450MatrixCodeNat M) hbool
  rwa [step108o450_codeMat_matrixCode_all] at hspan

private theorem step108o450s15_QtInv :
    (codeMat 171 : Mat3).transpose⁻¹ = (codeMat 485 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 171 : Mat3).transpose * (codeMat 485 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step108o450s15_contain :
    step108o450ActualSource15 ≤ actionW (codeMat 84) (codeMat 171) flatW_3 := by
  apply step108o450_spanCodes_le_of_gens [256, 129, 64, 33, 16, 9, 4, 3]
    (actionW (codeMat 84) (codeMat 171) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 2 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 171) (codeMat 2) = codeMat 256 := by
      unfold actionA
      rw [step108o450s15_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 485 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 197 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 197 (by decide)
    have hact : actionA (codeMat 84) (codeMat 171) (codeMat 197) = codeMat 129 := by
      unfold actionA
      rw [step108o450s15_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 197 * (codeMat 485 : Mat3).transpose = codeMat 129
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 3 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 84) (codeMat 171) (codeMat 3) = codeMat 64 := by
      unfold actionA
      rw [step108o450s15_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 3 * (codeMat 485 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 208 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 208 (by decide)
    have hact : actionA (codeMat 84) (codeMat 171) (codeMat 208) = codeMat 33 := by
      unfold actionA
      rw [step108o450s15_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 208 * (codeMat 485 : Mat3).transpose = codeMat 33
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 40 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 84) (codeMat 171) (codeMat 40) = codeMat 16 := by
      unfold actionA
      rw [step108o450s15_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 40 * (codeMat 485 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 216 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 216 (by decide)
    have hact : actionA (codeMat 84) (codeMat 171) (codeMat 216) = codeMat 9 := by
      unfold actionA
      rw [step108o450s15_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 216 * (codeMat 485 : Mat3).transpose = codeMat 9
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 171) (codeMat 128) = codeMat 4 := by
      unfold actionA
      rw [step108o450s15_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 485 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 171) (codeMat 384) = codeMat 3 := by
      unfold actionA
      rw [step108o450s15_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 485 : Mat3).transpose = codeMat 3
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact

theorem step108o450s15Dispatch :
    QuotientRankAtLeast (o450SourceU ⟨15, by omega⟩) 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 171 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 171) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 171) hP hQ flatW_3 9 flatSeed_3
  exact quotientRankAtLeast_mono (le_trans step108o450s15_sourceU_le step108o450s15_contain) hAct

-- Source 16: orbit 3, lb 9
def step108o450ActualSource16 : Submodule F2 Mat3 := spanCodes [256, 128, 65, 32, 17, 8, 5, 2]

private theorem step108o450s16_sourceU_le :
    (o450SourceU ⟨16, by omega⟩) ≤ step108o450ActualSource16 := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 128, 65, 32, 17, 8, 5, 2] (step108o450MatrixCodeNat M) = true := by
    change M ∈ kerEvalFunc (codeMat 17 + codeMat 68) at hM
    change evalFunc (codeMat 17 + codeMat 68) M = 0 at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 128, 65, 32, 17, 8, 5, 2] (step108o450MatrixCodeNat M) hbool
  rwa [step108o450_codeMat_matrixCode_all] at hspan

private theorem step108o450s16_QtInv :
    (codeMat 85 : Mat3).transpose⁻¹ = (codeMat 340 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 85 : Mat3).transpose * (codeMat 340 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step108o450s16_contain :
    step108o450ActualSource16 ≤ actionW (codeMat 84) (codeMat 85) flatW_3 := by
  apply step108o450_spanCodes_le_of_gens [256, 128, 65, 32, 17, 8, 5, 2]
    (actionW (codeMat 84) (codeMat 85) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 1 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 85) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step108o450s16_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 340 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 85) (codeMat 2) = codeMat 128 := by
      unfold actionA
      rw [step108o450s16_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 340 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 325 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 325 (by decide)
    have hact : actionA (codeMat 84) (codeMat 85) (codeMat 325) = codeMat 65 := by
      unfold actionA
      rw [step108o450s16_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 325 * (codeMat 340 : Mat3).transpose = codeMat 65
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 85) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step108o450s16_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 340 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 336 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 336 (by decide)
    have hact : actionA (codeMat 84) (codeMat 85) (codeMat 336) = codeMat 17 := by
      unfold actionA
      rw [step108o450s16_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 336 * (codeMat 340 : Mat3).transpose = codeMat 17
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 40 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 84) (codeMat 85) (codeMat 40) = codeMat 8 := by
      unfold actionA
      rw [step108o450s16_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 40 * (codeMat 340 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 85) (codeMat 256) = codeMat 5 := by
      unfold actionA
      rw [step108o450s16_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 340 : Mat3).transpose = codeMat 5
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 128 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 85) (codeMat 128) = codeMat 2 := by
      unfold actionA
      rw [step108o450s16_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 340 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact

theorem step108o450s16Dispatch :
    QuotientRankAtLeast (o450SourceU ⟨16, by omega⟩) 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 85 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 85) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 85) hP hQ flatW_3 9 flatSeed_3
  exact quotientRankAtLeast_mono (le_trans step108o450s16_sourceU_le step108o450s16_contain) hAct

-- Source 17: orbit 3, lb 9
def step108o450ActualSource17 : Submodule F2 Mat3 := spanCodes [257, 128, 64, 32, 17, 8, 4, 2]

private theorem step108o450s17_sourceU_le :
    (o450SourceU ⟨17, by omega⟩) ≤ step108o450ActualSource17 := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 128, 64, 32, 17, 8, 4, 2] (step108o450MatrixCodeNat M) = true := by
    change M ∈ kerEvalFunc (codeMat 256 + codeMat 17) at hM
    change evalFunc (codeMat 256 + codeMat 17) M = 0 at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 128, 64, 32, 17, 8, 4, 2] (step108o450MatrixCodeNat M) hbool
  rwa [step108o450_codeMat_matrixCode_all] at hspan

private theorem step108o450s17_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step108o450s17_contain :
    step108o450ActualSource17 ≤ actionW (codeMat 84) (codeMat 273) flatW_3 := by
  apply step108o450_spanCodes_le_of_gens [257, 128, 64, 32, 17, 8, 4, 2]
    (actionW (codeMat 84) (codeMat 273) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 68 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 68 (by decide)
    have hact : actionA (codeMat 84) (codeMat 273) (codeMat 68) = codeMat 257 := by
      unfold actionA
      rw [step108o450s17_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 68 * (codeMat 273 : Mat3).transpose = codeMat 257
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 273) (codeMat 2) = codeMat 128 := by
      unfold actionA
      rw [step108o450s17_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 273) (codeMat 1) = codeMat 64 := by
      unfold actionA
      rw [step108o450s17_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 32 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 84) (codeMat 273) (codeMat 32) = codeMat 32 := by
      unfold actionA
      rw [step108o450s17_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 32 * (codeMat 273 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 80 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 80 (by decide)
    have hact : actionA (codeMat 84) (codeMat 273) (codeMat 80) = codeMat 17 := by
      unfold actionA
      rw [step108o450s17_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 80 * (codeMat 273 : Mat3).transpose = codeMat 17
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 273) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step108o450s17_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 273 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 273) (codeMat 256) = codeMat 4 := by
      unfold actionA
      rw [step108o450s17_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 273 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 128 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 273) (codeMat 128) = codeMat 2 := by
      unfold actionA
      rw [step108o450s17_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 273 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step108o450_codeMat_mem_actionW_of_witness hw hact

theorem step108o450s17Dispatch :
    QuotientRankAtLeast (o450SourceU ⟨17, by omega⟩) 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 273) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 273) hP hQ flatW_3 9 flatSeed_3
  exact quotientRankAtLeast_mono (le_trans step108o450s17_sourceU_le step108o450s17_contain) hAct

theorem step108o450_all_dispatch (i : Fin 18) :
    QuotientRankAtLeast (o450SourceU i) (o450SourceLb i) := by
  fin_cases i
  · exact step108o450s0Dispatch
  · exact step108o450s1Dispatch
  · exact step108o450s2Dispatch
  · exact step108o450s3Dispatch
  · exact step108o450s4Dispatch
  · exact step108o450s5Dispatch
  · exact step108o450s6Dispatch
  · exact step108o450s7Dispatch
  · exact step108o450s8Dispatch
  · exact step108o450s9Dispatch
  · exact step108o450s10Dispatch
  · exact step108o450s11Dispatch
  · exact step108o450s12Dispatch
  · exact step108o450s13Dispatch
  · exact step108o450s14Dispatch
  · exact step108o450s15Dispatch
  · exact step108o450s16Dispatch
  · exact step108o450s17Dispatch

theorem step108_orbit450_lb18_unconditional :
    QuotientRankAtLeast o450W 18 :=
  o450Lb18 step108o450_all_dispatch

end QiushiMatmul
