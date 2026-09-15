import QiushiCodeSpanCore
import QiushiFlattenSeeds
import QiushiMonotonicity
import QiushiOrbit10FP
import QiushiOrbitTransport
import QiushiStep98Orbit67Consumer

set_option maxHeartbeats 800000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem step99o67_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step99o67MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step99o67_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step99o67MatrixCodeNat M) = M := by decide

lemma step99o67_codeMat_matrixCode (M : Mat3) :
    codeMat (step99o67MatrixCodeNat M) = M :=
  step99o67_codeMat_matrixCode_all M

private theorem step99o67_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step99o67_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

-- Source 0 (row 0): orbit 10, lb 12
def step99o67ActualSource0 : Submodule F2 Mat3 := spanCodes [260, 164, 68, 16, 8, 2, 1]

private theorem step99o67s0_sourceU_le :
    (o67SourceU ⟨0, by omega⟩) ≤ step99o67ActualSource0 := by
  intro M hM
  have hbool : spanContainsCodeCore [260, 164, 68, 16, 8, 2, 1] (step99o67MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 266 + codeMat 110) ⊓ kerEvalFunc (codeMat 160)) at hM
    change (evalFunc (codeMat 266 + codeMat 110) M = 0 ∧ evalFunc (codeMat 160) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 164, 68, 16, 8, 2, 1] (step99o67MatrixCodeNat M) hbool
  rwa [step99o67_codeMat_matrixCode] at hspan

private theorem step99o67s0_QtInv :
    (codeMat 314 : Mat3).transpose⁻¹ = (codeMat 271 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 314 : Mat3).transpose * (codeMat 271 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o67s0_targetSpan_le_action :
    step99o67ActualSource0 ≤ actionW (codeMat 266) (codeMat 314) orbit10W := by
  apply step99o67_spanCodes_le_of_gens [260, 164, 68, 16, 8, 2, 1]
    (actionW (codeMat 266) (codeMat 314) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 432 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 432 (by decide)
    have hact : actionA (codeMat 266) (codeMat 314) (codeMat 432) = codeMat 260 := by
      unfold actionA
      rw [step99o67s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 432 * (codeMat 271 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o67_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 246 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 246 (by decide)
    have hact : actionA (codeMat 266) (codeMat 314) (codeMat 246) = codeMat 164 := by
      unfold actionA
      rw [step99o67s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 246 * (codeMat 271 : Mat3).transpose = codeMat 164
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o67_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 176 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 176 (by decide)
    have hact : actionA (codeMat 266) (codeMat 314) (codeMat 176) = codeMat 68 := by
      unfold actionA
      rw [step99o67s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 176 * (codeMat 271 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o67_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 3 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 3 (by decide)
    have hact : actionA (codeMat 266) (codeMat 314) (codeMat 3) = codeMat 16 := by
      unfold actionA
      rw [step99o67s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 3 * (codeMat 271 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o67_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 314) (codeMat 2) = codeMat 8 := by
      unfold actionA
      rw [step99o67s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 271 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o67_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 24 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide)
    have hact : actionA (codeMat 266) (codeMat 314) (codeMat 24) = codeMat 2 := by
      unfold actionA
      rw [step99o67s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 24 * (codeMat 271 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o67_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 314) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step99o67s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 271 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o67_codeMat_mem_actionW_of_witness hw hact

theorem step99o67s0Dispatch :
    QuotientRankAtLeast (o67SourceU ⟨0, by omega⟩) 12 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 314 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 314) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 314) hP hQ orbit10W 12 orbit10_lb12
  have hMono : QuotientRankAtLeast step99o67ActualSource0 12 :=
    quotientRankAtLeast_mono step99o67s0_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o67s0_sourceU_le hMono

-- Source 1 (row 7): orbit 3, lb 9
def step99o67ActualSource1 : Submodule F2 Mat3 := spanCodes [258, 128, 64, 32, 16, 10, 4, 1]

private theorem step99o67s1_sourceU_le :
    (o67SourceU ⟨1, by omega⟩) ≤ step99o67ActualSource1 := by
  intro M hM
  have hbool : spanContainsCodeCore [258, 128, 64, 32, 16, 10, 4, 1] (step99o67MatrixCodeNat M) = true := by
    change M ∈ kerEvalFunc (codeMat 266) at hM
    change evalFunc (codeMat 266) M = 0 at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 128, 64, 32, 16, 10, 4, 1] (step99o67MatrixCodeNat M) hbool
  rwa [step99o67_codeMat_matrixCode] at hspan

private theorem step99o67s1_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o67s1_targetSpan_le_action :
    step99o67ActualSource1 ≤ actionW (codeMat 84) (codeMat 266) flatW_3 := by
  apply step99o67_spanCodes_le_of_gens [258, 128, 64, 32, 16, 10, 4, 1]
    (actionW (codeMat 84) (codeMat 266) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 68 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 68 (by decide)
    have hact : actionA (codeMat 84) (codeMat 266) (codeMat 68) = codeMat 258 := by
      unfold actionA
      rw [step99o67s1_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 68 * (codeMat 266 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o67_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 266) (codeMat 1) = codeMat 128 := by
      unfold actionA
      rw [step99o67s1_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o67_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 266) (codeMat 2) = codeMat 64 := by
      unfold actionA
      rw [step99o67s1_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 266 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o67_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 32 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 84) (codeMat 266) (codeMat 32) = codeMat 32 := by
      unfold actionA
      rw [step99o67s1_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 32 * (codeMat 266 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o67_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 266) (codeMat 8) = codeMat 16 := by
      unfold actionA
      rw [step99o67s1_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 266 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o67_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 80 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 80 (by decide)
    have hact : actionA (codeMat 84) (codeMat 266) (codeMat 80) = codeMat 10 := by
      unfold actionA
      rw [step99o67s1_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 80 * (codeMat 266 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o67_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 266) (codeMat 256) = codeMat 4 := by
      unfold actionA
      rw [step99o67s1_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 266 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o67_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 128 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 266) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step99o67s1_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o67_codeMat_mem_actionW_of_witness hw hact

theorem step99o67s1Dispatch :
    QuotientRankAtLeast (o67SourceU ⟨1, by omega⟩) 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 266) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 266) hP hQ flatW_3 9 flatSeed_3
  have hMono : QuotientRankAtLeast step99o67ActualSource1 9 :=
    quotientRankAtLeast_mono step99o67s1_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o67s1_sourceU_le hMono

-- Source 2 (row 8): orbit 3, lb 9
def step99o67ActualSource2 : Submodule F2 Mat3 := spanCodes [256, 128, 66, 34, 16, 10, 6, 1]

private theorem step99o67s2_sourceU_le :
    (o67SourceU ⟨2, by omega⟩) ≤ step99o67ActualSource2 := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 128, 66, 34, 16, 10, 6, 1] (step99o67MatrixCodeNat M) = true := by
    change M ∈ kerEvalFunc (codeMat 110) at hM
    change evalFunc (codeMat 110) M = 0 at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 128, 66, 34, 16, 10, 6, 1] (step99o67MatrixCodeNat M) hbool
  rwa [step99o67_codeMat_matrixCode] at hspan

private theorem step99o67s2_QtInv :
    (codeMat 110 : Mat3).transpose⁻¹ = (codeMat 444 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 110 : Mat3).transpose * (codeMat 444 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o67s2_targetSpan_le_action :
    step99o67ActualSource2 ≤ actionW (codeMat 84) (codeMat 110) flatW_3 := by
  apply step99o67_spanCodes_le_of_gens [256, 128, 66, 34, 16, 10, 6, 1]
    (actionW (codeMat 84) (codeMat 110) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 3 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 84) (codeMat 110) (codeMat 3) = codeMat 256 := by
      unfold actionA
      rw [step99o67s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 3 * (codeMat 444 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o67_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 110) (codeMat 1) = codeMat 128 := by
      unfold actionA
      rw [step99o67s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 444 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o67_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 70 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 70 (by decide)
    have hact : actionA (codeMat 84) (codeMat 110) (codeMat 70) = codeMat 66 := by
      unfold actionA
      rw [step99o67s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 70 * (codeMat 444 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o67_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 88 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 88 (by decide)
    have hact : actionA (codeMat 84) (codeMat 110) (codeMat 88) = codeMat 34 := by
      unfold actionA
      rw [step99o67s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 88 * (codeMat 444 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o67_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 110) (codeMat 8) = codeMat 16 := by
      unfold actionA
      rw [step99o67s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 444 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o67_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 112 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 112 (by decide)
    have hact : actionA (codeMat 84) (codeMat 110) (codeMat 112) = codeMat 10 := by
      unfold actionA
      rw [step99o67s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 112 * (codeMat 444 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o67_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 110) (codeMat 128) = codeMat 6 := by
      unfold actionA
      rw [step99o67s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 444 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o67_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 110) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step99o67s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 444 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o67_codeMat_mem_actionW_of_witness hw hact

theorem step99o67s2Dispatch :
    QuotientRankAtLeast (o67SourceU ⟨2, by omega⟩) 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 110 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 110) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 110) hP hQ flatW_3 9 flatSeed_3
  have hMono : QuotientRankAtLeast step99o67ActualSource2 9 :=
    quotientRankAtLeast_mono step99o67s2_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o67s2_sourceU_le hMono

-- Source 3 (row 9): orbit 3, lb 9
def step99o67ActualSource3 : Submodule F2 Mat3 := spanCodes [256, 130, 66, 32, 16, 10, 6, 1]

private theorem step99o67s3_sourceU_le :
    (o67SourceU ⟨3, by omega⟩) ≤ step99o67ActualSource3 := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 130, 66, 32, 16, 10, 6, 1] (step99o67MatrixCodeNat M) = true := by
    change M ∈ kerEvalFunc (codeMat 160 + codeMat 110) at hM
    change evalFunc (codeMat 160 + codeMat 110) M = 0 at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 130, 66, 32, 16, 10, 6, 1] (step99o67MatrixCodeNat M) hbool
  rwa [step99o67_codeMat_matrixCode] at hspan

private theorem step99o67s3_QtInv :
    (codeMat 206 : Mat3).transpose⁻¹ = (codeMat 498 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 206 : Mat3).transpose * (codeMat 498 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o67s3_targetSpan_le_action :
    step99o67ActualSource3 ≤ actionW (codeMat 84) (codeMat 206) flatW_3 := by
  apply step99o67_spanCodes_le_of_gens [256, 130, 66, 32, 16, 10, 6, 1]
    (actionW (codeMat 84) (codeMat 206) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 1 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 206) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step99o67s3_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 498 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o67_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 325 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 325 (by decide)
    have hact : actionA (codeMat 84) (codeMat 206) (codeMat 325) = codeMat 130 := by
      unfold actionA
      rw [step99o67s3_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 325 * (codeMat 498 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o67_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 326 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 326 (by decide)
    have hact : actionA (codeMat 84) (codeMat 206) (codeMat 326) = codeMat 66 := by
      unfold actionA
      rw [step99o67s3_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 326 * (codeMat 498 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o67_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 206) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step99o67s3_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 498 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o67_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 40 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 84) (codeMat 206) (codeMat 40) = codeMat 16 := by
      unfold actionA
      rw [step99o67s3_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 40 * (codeMat 498 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o67_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 368 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 368 (by decide)
    have hact : actionA (codeMat 84) (codeMat 206) (codeMat 368) = codeMat 10 := by
      unfold actionA
      rw [step99o67s3_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 368 * (codeMat 498 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o67_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 206) (codeMat 256) = codeMat 6 := by
      unfold actionA
      rw [step99o67s3_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 498 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o67_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 206) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step99o67s3_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 498 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o67_codeMat_mem_actionW_of_witness hw hact

theorem step99o67s3Dispatch :
    QuotientRankAtLeast (o67SourceU ⟨3, by omega⟩) 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 206 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 206) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 206) hP hQ flatW_3 9 flatSeed_3
  have hMono : QuotientRankAtLeast step99o67ActualSource3 9 :=
    quotientRankAtLeast_mono step99o67s3_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o67s3_sourceU_le hMono

-- Source 4 (row 10): orbit 3, lb 9
def step99o67ActualSource4 : Submodule F2 Mat3 := spanCodes [258, 130, 64, 34, 16, 10, 4, 1]

private theorem step99o67s4_sourceU_le :
    (o67SourceU ⟨4, by omega⟩) ≤ step99o67ActualSource4 := by
  intro M hM
  have hbool : spanContainsCodeCore [258, 130, 64, 34, 16, 10, 4, 1] (step99o67MatrixCodeNat M) = true := by
    change M ∈ kerEvalFunc (codeMat 266 + codeMat 160) at hM
    change evalFunc (codeMat 266 + codeMat 160) M = 0 at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 130, 64, 34, 16, 10, 4, 1] (step99o67MatrixCodeNat M) hbool
  rwa [step99o67_codeMat_matrixCode] at hspan

private theorem step99o67s4_QtInv :
    (codeMat 426 : Mat3).transpose⁻¹ = (codeMat 335 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 426 : Mat3).transpose * (codeMat 335 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o67s4_targetSpan_le_action :
    step99o67ActualSource4 ≤ actionW (codeMat 84) (codeMat 426) flatW_3 := by
  apply step99o67_spanCodes_le_of_gens [258, 130, 64, 34, 16, 10, 4, 1]
    (actionW (codeMat 84) (codeMat 426) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 326 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 326 (by decide)
    have hact : actionA (codeMat 84) (codeMat 426) (codeMat 326) = codeMat 258 := by
      unfold actionA
      rw [step99o67s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 326 * (codeMat 335 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o67_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 325 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 325 (by decide)
    have hact : actionA (codeMat 84) (codeMat 426) (codeMat 325) = codeMat 130 := by
      unfold actionA
      rw [step99o67s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 325 * (codeMat 335 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o67_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 426) (codeMat 2) = codeMat 64 := by
      unfold actionA
      rw [step99o67s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 335 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o67_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 368 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 368 (by decide)
    have hact : actionA (codeMat 84) (codeMat 426) (codeMat 368) = codeMat 34 := by
      unfold actionA
      rw [step99o67s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 368 * (codeMat 335 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o67_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 40 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 84) (codeMat 426) (codeMat 40) = codeMat 16 := by
      unfold actionA
      rw [step99o67s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 40 * (codeMat 335 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o67_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 336 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 336 (by decide)
    have hact : actionA (codeMat 84) (codeMat 426) (codeMat 336) = codeMat 10 := by
      unfold actionA
      rw [step99o67s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 336 * (codeMat 335 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o67_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 426) (codeMat 384) = codeMat 4 := by
      unfold actionA
      rw [step99o67s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 335 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o67_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 128 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 426) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step99o67s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 335 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o67_codeMat_mem_actionW_of_witness hw hact

theorem step99o67s4Dispatch :
    QuotientRankAtLeast (o67SourceU ⟨4, by omega⟩) 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 426 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 426) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 426) hP hQ flatW_3 9 flatSeed_3
  have hMono : QuotientRankAtLeast step99o67ActualSource4 9 :=
    quotientRankAtLeast_mono step99o67s4_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o67s4_sourceU_le hMono

theorem step99o67_all_dispatch (i : Fin 5) :
    QuotientRankAtLeast (o67SourceU i) (o67SourceLb i) := by
  fin_cases i
  · exact step99o67s0Dispatch
  · exact step99o67s1Dispatch
  · exact step99o67s2Dispatch
  · exact step99o67s3Dispatch
  · exact step99o67s4Dispatch

theorem step99_orbit67_lb15_unconditional :
    QuotientRankAtLeast o67W 15 :=
  o67Lb15 step99o67_all_dispatch

end QiushiMatmul
