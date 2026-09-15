import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiStep98Orbit237Consumer
import QiushiStep99Orbit56Dispatch
import QiushiStep99Orbit68Dispatch
import QiushiStep99Orbit77Dispatch
import QiushiTransposeTransport

set_option maxHeartbeats 800000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem step99o237_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step99o237MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step99o237_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step99o237MatrixCodeNat M) = M := by decide

lemma step99o237_codeMat_matrixCode (M : Mat3) :
    codeMat (step99o237MatrixCodeNat M) = M :=
  step99o237_codeMat_matrixCode_all M

private theorem step99o237_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step99o237_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

private theorem step99o237_codeMat_mem_transposeW_of_witness
    {V : Submodule F2 Mat3} {pre tpre : Nat}
    (h_mem : codeMat tpre ∈ V)
    (h_trans : (codeMat tpre : Mat3).transpose = codeMat pre) :
    codeMat pre ∈ transposeW V := by
  change ∃ X, X ∈ V ∧ transposeLinearMap X = codeMat pre
  exact ⟨codeMat tpre, h_mem, h_trans⟩

-- Source 0 (row 0): orbit 77, lb 15
def step99o237ActualSource0 : Submodule F2 Mat3 := spanCodes [256, 130, 96, 20, 10, 1]

private theorem step99o237s0_sourceU_le :
    (o237SourceU ⟨0, by omega⟩) ≤ step99o237ActualSource0 := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 130, 96, 20, 10, 1] (step99o237MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 138) ⊓ kerEvalFunc (codeMat 96)) ⊓ kerEvalFunc (codeMat 20)) at hM
    change ((evalFunc (codeMat 138) M = 0 ∧ evalFunc (codeMat 96) M = 0) ∧ evalFunc (codeMat 20) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 130, 96, 20, 10, 1] (step99o237MatrixCodeNat M) hbool
  rwa [step99o237_codeMat_matrixCode] at hspan

private theorem step99o237s0_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o237s0_targetSpan_le_action :
    step99o237ActualSource0 ≤ actionW (codeMat 84) (codeMat 140) o77W := by
  apply step99o237_spanCodes_le_of_gens [256, 130, 96, 20, 10, 1]
    (actionW (codeMat 84) (codeMat 140) o77W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 1 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step99o237s0_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 260 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 260 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 260) = codeMat 130 := by
      unfold actionA
      rw [step99o237s0_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 260 * (codeMat 98 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 10 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 10) = codeMat 96 := by
      unfold actionA
      rw [step99o237s0_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 10 * (codeMat 98 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 96 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 96 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 96) = codeMat 20 := by
      unfold actionA
      rw [step99o237s0_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 96 * (codeMat 98 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 272 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 272 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 272) = codeMat 10 := by
      unfold actionA
      rw [step99o237s0_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 272 * (codeMat 98 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step99o237s0_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact

theorem step99o237s0Dispatch :
    QuotientRankAtLeast (o237SourceU ⟨0, by omega⟩) 15 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 140) o77W) 15 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 140) hP hQ o77W 15 step99_orbit77_lb15_unconditional
  have hMono : QuotientRankAtLeast step99o237ActualSource0 15 :=
    quotientRankAtLeast_mono step99o237s0_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o237s0_sourceU_le hMono

-- Source 1 (row 1): orbit 77, lb 15
def step99o237ActualSource1 : Submodule F2 Mat3 := spanCodes [262, 132, 96, 20, 12, 1]

private theorem step99o237s1_sourceU_le :
    (o237SourceU ⟨1, by omega⟩) ≤ step99o237ActualSource1 := by
  intro M hM
  have hbool : spanContainsCodeCore [262, 132, 96, 20, 12, 1] (step99o237MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 258) ⊓ kerEvalFunc (codeMat 138 + codeMat 20)) ⊓ kerEvalFunc (codeMat 96)) at hM
    change ((evalFunc (codeMat 258) M = 0 ∧ evalFunc (codeMat 138 + codeMat 20) M = 0) ∧ evalFunc (codeMat 96) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 132, 96, 20, 12, 1] (step99o237MatrixCodeNat M) hbool
  rwa [step99o237_codeMat_matrixCode] at hspan

private theorem step99o237s1_QtInv :
    (codeMat 305 : Mat3).transpose⁻¹ = (codeMat 305 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 305 : Mat3).transpose * (codeMat 305 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o237s1_targetSpan_le_transposeAction :
    step99o237ActualSource1 ≤ transposeW (actionW (codeMat 233) (codeMat 305) o77W) := by
  apply step99o237_spanCodes_le_of_gens [262, 132, 96, 20, 12, 1]
    (transposeW (actionW (codeMat 233) (codeMat 305) o77W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    -- g=262, g^T=328; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 126 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 126 (by decide)
    have hact : actionA (codeMat 233) (codeMat 305) (codeMat 126) = codeMat 328 := by
      unfold actionA
      rw [step99o237s1_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 126 * (codeMat 305 : Mat3).transpose = codeMat 328
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 328 ∈ actionW (codeMat 233) (codeMat 305) o77W :=
      step99o237_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 328 : Mat3).transpose = codeMat 262 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h1
    -- g=132, g^T=96; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 399 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 399 (by decide)
    have hact : actionA (codeMat 233) (codeMat 305) (codeMat 399) = codeMat 96 := by
      unfold actionA
      rw [step99o237s1_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 399 * (codeMat 305 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 96 ∈ actionW (codeMat 233) (codeMat 305) o77W :=
      step99o237_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 96 : Mat3).transpose = codeMat 132 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h2
    -- g=96, g^T=132; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 20 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 20 (by decide)
    have hact : actionA (codeMat 233) (codeMat 305) (codeMat 20) = codeMat 132 := by
      unfold actionA
      rw [step99o237s1_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 20 * (codeMat 305 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 132 ∈ actionW (codeMat 233) (codeMat 305) o77W :=
      step99o237_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 132 : Mat3).transpose = codeMat 96 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h3
    -- g=20, g^T=80; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 139 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 139 (by decide)
    have hact : actionA (codeMat 233) (codeMat 305) (codeMat 139) = codeMat 80 := by
      unfold actionA
      rw [step99o237s1_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 139 * (codeMat 305 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 80 ∈ actionW (codeMat 233) (codeMat 305) o77W :=
      step99o237_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 80 : Mat3).transpose = codeMat 20 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h4
    -- g=12, g^T=66; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 11 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 233) (codeMat 305) (codeMat 11) = codeMat 66 := by
      unfold actionA
      rw [step99o237s1_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 11 * (codeMat 305 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 66 ∈ actionW (codeMat 233) (codeMat 305) o77W :=
      step99o237_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 66 : Mat3).transpose = codeMat 12 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h5
    -- g=1, g^T=1; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 1 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 233) (codeMat 305) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step99o237s1_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 1 * (codeMat 305 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 1 ∈ actionW (codeMat 233) (codeMat 305) o77W :=
      step99o237_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 1 : Mat3).transpose = codeMat 1 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_transposeW_of_witness hmemAction htrans

theorem step99o237s1Dispatch :
    QuotientRankAtLeast (o237SourceU ⟨1, by omega⟩) 15 := by
  have hP : Invertible (codeMat 233 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 233) (codeMat 305) o77W) 15 :=
    @quotientRankAtLeast_action (codeMat 233) (codeMat 305) hP hQ o77W 15 step99_orbit77_lb15_unconditional
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 233) (codeMat 305) o77W)) 15 :=
    quotientRankAtLeast_transpose hAct
  have hMono : QuotientRankAtLeast step99o237ActualSource1 15 :=
    quotientRankAtLeast_mono step99o237s1_targetSpan_le_transposeAction hT
  exact quotientRankAtLeast_mono step99o237s1_sourceU_le hMono

-- Source 2 (row 2): orbit 77, lb 15
def step99o237ActualSource2 : Submodule F2 Mat3 := spanCodes [266, 136, 66, 34, 20, 1]

private theorem step99o237s2_sourceU_le :
    (o237SourceU ⟨2, by omega⟩) ≤ step99o237ActualSource2 := by
  intro M hM
  have hbool : spanContainsCodeCore [266, 136, 66, 34, 20, 1] (step99o237MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 258 + codeMat 96) ⊓ kerEvalFunc (codeMat 138 + codeMat 96)) ⊓ kerEvalFunc (codeMat 20)) at hM
    change ((evalFunc (codeMat 258 + codeMat 96) M = 0 ∧ evalFunc (codeMat 138 + codeMat 96) M = 0) ∧ evalFunc (codeMat 20) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [266, 136, 66, 34, 20, 1] (step99o237MatrixCodeNat M) hbool
  rwa [step99o237_codeMat_matrixCode] at hspan

private theorem step99o237s2_QtInv :
    (codeMat 282 : Mat3).transpose⁻¹ = (codeMat 267 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 282 : Mat3).transpose * (codeMat 267 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o237s2_targetSpan_le_transposeAction :
    step99o237ActualSource2 ≤ transposeW (actionW (codeMat 86) (codeMat 282) o77W) := by
  apply step99o237_spanCodes_le_of_gens [266, 136, 66, 34, 20, 1]
    (transposeW (actionW (codeMat 86) (codeMat 282) o77W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    -- g=266, g^T=266; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 244 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 244 (by decide)
    have hact : actionA (codeMat 86) (codeMat 282) (codeMat 244) = codeMat 266 := by
      unfold actionA
      rw [step99o237s2_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 244 * (codeMat 267 : Mat3).transpose = codeMat 266
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 266 ∈ actionW (codeMat 86) (codeMat 282) o77W :=
      step99o237_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 266 : Mat3).transpose = codeMat 266 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h1
    -- g=136, g^T=34; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 224 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 224 (by decide)
    have hact : actionA (codeMat 86) (codeMat 282) (codeMat 224) = codeMat 34 := by
      unfold actionA
      rw [step99o237s2_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 224 * (codeMat 267 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 34 ∈ actionW (codeMat 86) (codeMat 282) o77W :=
      step99o237_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 34 : Mat3).transpose = codeMat 136 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h2
    -- g=66, g^T=12; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 272 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 272 (by decide)
    have hact : actionA (codeMat 86) (codeMat 282) (codeMat 272) = codeMat 12 := by
      unfold actionA
      rw [step99o237s2_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 272 * (codeMat 267 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 12 ∈ actionW (codeMat 86) (codeMat 282) o77W :=
      step99o237_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 12 : Mat3).transpose = codeMat 66 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h3
    -- g=34, g^T=136; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 11 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 86) (codeMat 282) (codeMat 11) = codeMat 136 := by
      unfold actionA
      rw [step99o237s2_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 11 * (codeMat 267 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 136 ∈ actionW (codeMat 86) (codeMat 282) o77W :=
      step99o237_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 136 : Mat3).transpose = codeMat 34 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h4
    -- g=20, g^T=80; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 10 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 86) (codeMat 282) (codeMat 10) = codeMat 80 := by
      unfold actionA
      rw [step99o237s2_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 10 * (codeMat 267 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 80 ∈ actionW (codeMat 86) (codeMat 282) o77W :=
      step99o237_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 80 : Mat3).transpose = codeMat 20 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h5
    -- g=1, g^T=1; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 128 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 86) (codeMat 282) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step99o237s2_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 128 * (codeMat 267 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 1 ∈ actionW (codeMat 86) (codeMat 282) o77W :=
      step99o237_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 1 : Mat3).transpose = codeMat 1 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_transposeW_of_witness hmemAction htrans

theorem step99o237s2Dispatch :
    QuotientRankAtLeast (o237SourceU ⟨2, by omega⟩) 15 := by
  have hP : Invertible (codeMat 86 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 282 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 86) (codeMat 282) o77W) 15 :=
    @quotientRankAtLeast_action (codeMat 86) (codeMat 282) hP hQ o77W 15 step99_orbit77_lb15_unconditional
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 86) (codeMat 282) o77W)) 15 :=
    quotientRankAtLeast_transpose hAct
  have hMono : QuotientRankAtLeast step99o237ActualSource2 15 :=
    quotientRankAtLeast_mono step99o237s2_targetSpan_le_transposeAction hT
  exact quotientRankAtLeast_mono step99o237s2_sourceU_le hMono

-- Source 3 (row 3): orbit 77, lb 15
def step99o237ActualSource3 : Submodule F2 Mat3 := spanCodes [266, 136, 70, 38, 20, 1]

private theorem step99o237s3_sourceU_le :
    (o237SourceU ⟨3, by omega⟩) ≤ step99o237ActualSource3 := by
  intro M hM
  have hbool : spanContainsCodeCore [266, 136, 70, 38, 20, 1] (step99o237MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 258 + codeMat 20) ⊓ kerEvalFunc (codeMat 138 + codeMat 20)) ⊓ kerEvalFunc (codeMat 96 + codeMat 20)) at hM
    change ((evalFunc (codeMat 258 + codeMat 20) M = 0 ∧ evalFunc (codeMat 138 + codeMat 20) M = 0) ∧ evalFunc (codeMat 96 + codeMat 20) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [266, 136, 70, 38, 20, 1] (step99o237MatrixCodeNat M) hbool
  rwa [step99o237_codeMat_matrixCode] at hspan

private theorem step99o237s3_QtInv :
    (codeMat 500 : Mat3).transpose⁻¹ = (codeMat 94 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 500 : Mat3).transpose * (codeMat 94 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o237s3_targetSpan_le_action :
    step99o237ActualSource3 ≤ actionW (codeMat 486) (codeMat 500) o77W := by
  apply step99o237_spanCodes_le_of_gens [266, 136, 70, 38, 20, 1]
    (actionW (codeMat 486) (codeMat 500) o77W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 410 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 410 (by decide)
    have hact : actionA (codeMat 486) (codeMat 500) (codeMat 410) = codeMat 266 := by
      unfold actionA
      rw [step99o237s3_QtInv]
      show (codeMat 486 : Mat3).transpose * codeMat 410 * (codeMat 94 : Mat3).transpose = codeMat 266
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 20 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 20 (by decide)
    have hact : actionA (codeMat 486) (codeMat 500) (codeMat 20) = codeMat 136 := by
      unfold actionA
      rw [step99o237s3_QtInv]
      show (codeMat 486 : Mat3).transpose * codeMat 20 * (codeMat 94 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 97 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 97 (by decide)
    have hact : actionA (codeMat 486) (codeMat 500) (codeMat 97) = codeMat 70 := by
      unfold actionA
      rw [step99o237s3_QtInv]
      show (codeMat 486 : Mat3).transpose * codeMat 97 * (codeMat 94 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 126 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 126 (by decide)
    have hact : actionA (codeMat 486) (codeMat 500) (codeMat 126) = codeMat 38 := by
      unfold actionA
      rw [step99o237s3_QtInv]
      show (codeMat 486 : Mat3).transpose * codeMat 126 * (codeMat 94 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 497 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 497 (by decide)
    have hact : actionA (codeMat 486) (codeMat 500) (codeMat 497) = codeMat 20 := by
      unfold actionA
      rw [step99o237s3_QtInv]
      show (codeMat 486 : Mat3).transpose * codeMat 497 * (codeMat 94 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 260 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 260 (by decide)
    have hact : actionA (codeMat 486) (codeMat 500) (codeMat 260) = codeMat 1 := by
      unfold actionA
      rw [step99o237s3_QtInv]
      show (codeMat 486 : Mat3).transpose * codeMat 260 * (codeMat 94 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact

theorem step99o237s3Dispatch :
    QuotientRankAtLeast (o237SourceU ⟨3, by omega⟩) 15 := by
  have hP : Invertible (codeMat 486 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 500 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 486) (codeMat 500) o77W) 15 :=
    @quotientRankAtLeast_action (codeMat 486) (codeMat 500) hP hQ o77W 15 step99_orbit77_lb15_unconditional
  have hMono : QuotientRankAtLeast step99o237ActualSource3 15 :=
    quotientRankAtLeast_mono step99o237s3_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o237s3_sourceU_le hMono

-- Source 4 (row 4): orbit 77, lb 15
def step99o237ActualSource4 : Submodule F2 Mat3 := spanCodes [266, 136, 76, 44, 20, 1]

private theorem step99o237s4_sourceU_le :
    (o237SourceU ⟨4, by omega⟩) ≤ step99o237ActualSource4 := by
  intro M hM
  have hbool : spanContainsCodeCore [266, 136, 76, 44, 20, 1] (step99o237MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 258) ⊓ kerEvalFunc (codeMat 138 + codeMat 20)) ⊓ kerEvalFunc (codeMat 96 + codeMat 20)) at hM
    change ((evalFunc (codeMat 258) M = 0 ∧ evalFunc (codeMat 138 + codeMat 20) M = 0) ∧ evalFunc (codeMat 96 + codeMat 20) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [266, 136, 76, 44, 20, 1] (step99o237MatrixCodeNat M) hbool
  rwa [step99o237_codeMat_matrixCode] at hspan

private theorem step99o237s4_QtInv :
    (codeMat 342 : Mat3).transpose⁻¹ = (codeMat 215 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 342 : Mat3).transpose * (codeMat 215 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o237s4_targetSpan_le_action :
    step99o237ActualSource4 ≤ actionW (codeMat 187) (codeMat 342) o77W := by
  apply step99o237_spanCodes_le_of_gens [266, 136, 76, 44, 20, 1]
    (actionW (codeMat 187) (codeMat 342) o77W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 494 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 494 (by decide)
    have hact : actionA (codeMat 187) (codeMat 342) (codeMat 494) = codeMat 266 := by
      unfold actionA
      rw [step99o237s4_QtInv]
      show (codeMat 187 : Mat3).transpose * codeMat 494 * (codeMat 215 : Mat3).transpose = codeMat 266
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 283 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 283 (by decide)
    have hact : actionA (codeMat 187) (codeMat 342) (codeMat 283) = codeMat 136 := by
      unfold actionA
      rw [step99o237s4_QtInv]
      show (codeMat 187 : Mat3).transpose * codeMat 283 * (codeMat 215 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 97 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 97 (by decide)
    have hact : actionA (codeMat 187) (codeMat 342) (codeMat 97) = codeMat 76 := by
      unfold actionA
      rw [step99o237s4_QtInv]
      show (codeMat 187 : Mat3).transpose * codeMat 97 * (codeMat 215 : Mat3).transpose = codeMat 76
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 261 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 261 (by decide)
    have hact : actionA (codeMat 187) (codeMat 342) (codeMat 261) = codeMat 44 := by
      unfold actionA
      rw [step99o237s4_QtInv]
      show (codeMat 187 : Mat3).transpose * codeMat 261 * (codeMat 215 : Mat3).transpose = codeMat 44
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 389 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 389 (by decide)
    have hact : actionA (codeMat 187) (codeMat 342) (codeMat 389) = codeMat 20 := by
      unfold actionA
      rw [step99o237s4_QtInv]
      show (codeMat 187 : Mat3).transpose * codeMat 389 * (codeMat 215 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 260 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 260 (by decide)
    have hact : actionA (codeMat 187) (codeMat 342) (codeMat 260) = codeMat 1 := by
      unfold actionA
      rw [step99o237s4_QtInv]
      show (codeMat 187 : Mat3).transpose * codeMat 260 * (codeMat 215 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact

theorem step99o237s4Dispatch :
    QuotientRankAtLeast (o237SourceU ⟨4, by omega⟩) 15 := by
  have hP : Invertible (codeMat 187 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 342 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 187) (codeMat 342) o77W) 15 :=
    @quotientRankAtLeast_action (codeMat 187) (codeMat 342) hP hQ o77W 15 step99_orbit77_lb15_unconditional
  have hMono : QuotientRankAtLeast step99o237ActualSource4 15 :=
    quotientRankAtLeast_mono step99o237s4_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o237s4_sourceU_le hMono

-- Source 5 (row 5): orbit 77, lb 15
def step99o237ActualSource5 : Submodule F2 Mat3 := spanCodes [266, 136, 78, 46, 20, 1]

private theorem step99o237s5_sourceU_le :
    (o237SourceU ⟨5, by omega⟩) ≤ step99o237ActualSource5 := by
  intro M hM
  have hbool : spanContainsCodeCore [266, 136, 78, 46, 20, 1] (step99o237MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 258 + codeMat 20) ⊓ kerEvalFunc (codeMat 138)) ⊓ kerEvalFunc (codeMat 96 + codeMat 20)) at hM
    change ((evalFunc (codeMat 258 + codeMat 20) M = 0 ∧ evalFunc (codeMat 138) M = 0) ∧ evalFunc (codeMat 96 + codeMat 20) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [266, 136, 78, 46, 20, 1] (step99o237MatrixCodeNat M) hbool
  rwa [step99o237_codeMat_matrixCode] at hspan

private theorem step99o237s5_QtInv :
    (codeMat 370 : Mat3).transpose⁻¹ = (codeMat 207 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 370 : Mat3).transpose * (codeMat 207 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o237s5_targetSpan_le_transposeAction :
    step99o237ActualSource5 ≤ transposeW (actionW (codeMat 372) (codeMat 370) o77W) := by
  apply step99o237_spanCodes_le_of_gens [266, 136, 78, 46, 20, 1]
    (transposeW (actionW (codeMat 372) (codeMat 370) o77W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    -- g=266, g^T=266; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 225 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 225 (by decide)
    have hact : actionA (codeMat 372) (codeMat 370) (codeMat 225) = codeMat 266 := by
      unfold actionA
      rw [step99o237s5_QtInv]
      show (codeMat 372 : Mat3).transpose * codeMat 225 * (codeMat 207 : Mat3).transpose = codeMat 266
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 266 ∈ actionW (codeMat 372) (codeMat 370) o77W :=
      step99o237_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 266 : Mat3).transpose = codeMat 266 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h1
    -- g=136, g^T=34; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 245 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 245 (by decide)
    have hact : actionA (codeMat 372) (codeMat 370) (codeMat 245) = codeMat 34 := by
      unfold actionA
      rw [step99o237s5_QtInv]
      show (codeMat 372 : Mat3).transpose * codeMat 245 * (codeMat 207 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 34 ∈ actionW (codeMat 372) (codeMat 370) o77W :=
      step99o237_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 34 : Mat3).transpose = codeMat 136 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h2
    -- g=78, g^T=78; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 357 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 357 (by decide)
    have hact : actionA (codeMat 372) (codeMat 370) (codeMat 357) = codeMat 78 := by
      unfold actionA
      rw [step99o237s5_QtInv]
      show (codeMat 372 : Mat3).transpose * codeMat 357 * (codeMat 207 : Mat3).transpose = codeMat 78
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 78 ∈ actionW (codeMat 372) (codeMat 370) o77W :=
      step99o237_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 78 : Mat3).transpose = codeMat 78 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h3
    -- g=46, g^T=202; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 224 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 224 (by decide)
    have hact : actionA (codeMat 372) (codeMat 370) (codeMat 224) = codeMat 202 := by
      unfold actionA
      rw [step99o237s5_QtInv]
      show (codeMat 372 : Mat3).transpose * codeMat 224 * (codeMat 207 : Mat3).transpose = codeMat 202
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 202 ∈ actionW (codeMat 372) (codeMat 370) o77W :=
      step99o237_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 202 : Mat3).transpose = codeMat 46 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h4
    -- g=20, g^T=80; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 31 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 31 (by decide)
    have hact : actionA (codeMat 372) (codeMat 370) (codeMat 31) = codeMat 80 := by
      unfold actionA
      rw [step99o237s5_QtInv]
      show (codeMat 372 : Mat3).transpose * codeMat 31 * (codeMat 207 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 80 ∈ actionW (codeMat 372) (codeMat 370) o77W :=
      step99o237_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 80 : Mat3).transpose = codeMat 20 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h5
    -- g=1, g^T=1; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 260 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 260 (by decide)
    have hact : actionA (codeMat 372) (codeMat 370) (codeMat 260) = codeMat 1 := by
      unfold actionA
      rw [step99o237s5_QtInv]
      show (codeMat 372 : Mat3).transpose * codeMat 260 * (codeMat 207 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 1 ∈ actionW (codeMat 372) (codeMat 370) o77W :=
      step99o237_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 1 : Mat3).transpose = codeMat 1 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_transposeW_of_witness hmemAction htrans

theorem step99o237s5Dispatch :
    QuotientRankAtLeast (o237SourceU ⟨5, by omega⟩) 15 := by
  have hP : Invertible (codeMat 372 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 370 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 372) (codeMat 370) o77W) 15 :=
    @quotientRankAtLeast_action (codeMat 372) (codeMat 370) hP hQ o77W 15 step99_orbit77_lb15_unconditional
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 372) (codeMat 370) o77W)) 15 :=
    quotientRankAtLeast_transpose hAct
  have hMono : QuotientRankAtLeast step99o237ActualSource5 15 :=
    quotientRankAtLeast_mono step99o237s5_targetSpan_le_transposeAction hT
  exact quotientRankAtLeast_mono step99o237s5_sourceU_le hMono

-- Source 6 (row 6): orbit 56, lb 14
def step99o237ActualSource6 : Submodule F2 Mat3 := spanCodes [264, 136, 96, 20, 2, 1]

private theorem step99o237s6_sourceU_le :
    (o237SourceU ⟨6, by omega⟩) ≤ step99o237ActualSource6 := by
  intro M hM
  have hbool : spanContainsCodeCore [264, 136, 96, 20, 2, 1] (step99o237MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 258 + codeMat 138) ⊓ kerEvalFunc (codeMat 96)) ⊓ kerEvalFunc (codeMat 20)) at hM
    change ((evalFunc (codeMat 258 + codeMat 138) M = 0 ∧ evalFunc (codeMat 96) M = 0) ∧ evalFunc (codeMat 20) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [264, 136, 96, 20, 2, 1] (step99o237MatrixCodeNat M) hbool
  rwa [step99o237_codeMat_matrixCode] at hspan

private theorem step99o237s6_QtInv :
    (codeMat 270 : Mat3).transpose⁻¹ = (codeMat 298 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 270 : Mat3).transpose * (codeMat 298 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o237s6_targetSpan_le_action :
    step99o237ActualSource6 ≤ actionW (codeMat 281) (codeMat 270) o56W := by
  apply step99o237_spanCodes_le_of_gens [264, 136, 96, 20, 2, 1]
    (actionW (codeMat 281) (codeMat 270) o56W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 338 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 338 (by decide)
    have hact : actionA (codeMat 281) (codeMat 270) (codeMat 338) = codeMat 264 := by
      unfold actionA
      rw [step99o237s6_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 338 * (codeMat 298 : Mat3).transpose = codeMat 264
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 82 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 82 (by decide)
    have hact : actionA (codeMat 281) (codeMat 270) (codeMat 82) = codeMat 136 := by
      unfold actionA
      rw [step99o237s6_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 82 * (codeMat 298 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 173 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 173 (by decide)
    have hact : actionA (codeMat 281) (codeMat 270) (codeMat 173) = codeMat 96 := by
      unfold actionA
      rw [step99o237s6_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 173 * (codeMat 298 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 12 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 12 (by decide)
    have hact : actionA (codeMat 281) (codeMat 270) (codeMat 12) = codeMat 20 := by
      unfold actionA
      rw [step99o237s6_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 12 * (codeMat 298 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 281) (codeMat 270) (codeMat 1) = codeMat 2 := by
      unfold actionA
      rw [step99o237s6_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 1 * (codeMat 298 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 281) (codeMat 270) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step99o237s6_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 2 * (codeMat 298 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact

theorem step99o237s6Dispatch :
    QuotientRankAtLeast (o237SourceU ⟨6, by omega⟩) 14 := by
  have hP : Invertible (codeMat 281 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 270 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 281) (codeMat 270) o56W) 14 :=
    @quotientRankAtLeast_action (codeMat 281) (codeMat 270) hP hQ o56W 14 step99_orbit56_lb14_unconditional
  have hMono : QuotientRankAtLeast step99o237ActualSource6 14 :=
    quotientRankAtLeast_mono step99o237s6_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o237s6_sourceU_le hMono

-- Source 7 (row 7): orbit 56, lb 14
def step99o237ActualSource7 : Submodule F2 Mat3 := spanCodes [266, 136, 96, 16, 4, 1]

private theorem step99o237s7_sourceU_le :
    (o237SourceU ⟨7, by omega⟩) ≤ step99o237ActualSource7 := by
  intro M hM
  have hbool : spanContainsCodeCore [266, 136, 96, 16, 4, 1] (step99o237MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 258) ⊓ kerEvalFunc (codeMat 138)) ⊓ kerEvalFunc (codeMat 96)) at hM
    change ((evalFunc (codeMat 258) M = 0 ∧ evalFunc (codeMat 138) M = 0) ∧ evalFunc (codeMat 96) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [266, 136, 96, 16, 4, 1] (step99o237MatrixCodeNat M) hbool
  rwa [step99o237_codeMat_matrixCode] at hspan

private theorem step99o237s7_QtInv :
    (codeMat 172 : Mat3).transpose⁻¹ = (codeMat 99 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 172 : Mat3).transpose * (codeMat 99 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o237s7_targetSpan_le_action :
    step99o237ActualSource7 ≤ actionW (codeMat 177) (codeMat 172) o56W := by
  apply step99o237_spanCodes_le_of_gens [266, 136, 96, 16, 4, 1]
    (actionW (codeMat 177) (codeMat 172) o56W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 92 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 92 (by decide)
    have hact : actionA (codeMat 177) (codeMat 172) (codeMat 92) = codeMat 266 := by
      unfold actionA
      rw [step99o237s7_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 92 * (codeMat 99 : Mat3).transpose = codeMat 266
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 416 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 416 (by decide)
    have hact : actionA (codeMat 177) (codeMat 172) (codeMat 416) = codeMat 136 := by
      unfold actionA
      rw [step99o237s7_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 416 * (codeMat 99 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 80 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 80 (by decide)
    have hact : actionA (codeMat 177) (codeMat 172) (codeMat 80) = codeMat 96 := by
      unfold actionA
      rw [step99o237s7_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 80 * (codeMat 99 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 177) (codeMat 172) (codeMat 256) = codeMat 16 := by
      unfold actionA
      rw [step99o237s7_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 256 * (codeMat 99 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 177) (codeMat 172) (codeMat 3) = codeMat 4 := by
      unfold actionA
      rw [step99o237s7_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 3 * (codeMat 99 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 177) (codeMat 172) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step99o237s7_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 2 * (codeMat 99 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact

theorem step99o237s7Dispatch :
    QuotientRankAtLeast (o237SourceU ⟨7, by omega⟩) 14 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 172 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 172) o56W) 14 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 172) hP hQ o56W 14 step99_orbit56_lb14_unconditional
  have hMono : QuotientRankAtLeast step99o237ActualSource7 14 :=
    quotientRankAtLeast_mono step99o237s7_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o237s7_sourceU_le hMono

-- Source 8 (row 8): orbit 56, lb 14
def step99o237ActualSource8 : Submodule F2 Mat3 := spanCodes [266, 136, 96, 18, 6, 1]

private theorem step99o237s8_sourceU_le :
    (o237SourceU ⟨8, by omega⟩) ≤ step99o237ActualSource8 := by
  intro M hM
  have hbool : spanContainsCodeCore [266, 136, 96, 18, 6, 1] (step99o237MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 258 + codeMat 20) ⊓ kerEvalFunc (codeMat 138 + codeMat 20)) ⊓ kerEvalFunc (codeMat 96)) at hM
    change ((evalFunc (codeMat 258 + codeMat 20) M = 0 ∧ evalFunc (codeMat 138 + codeMat 20) M = 0) ∧ evalFunc (codeMat 96) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [266, 136, 96, 18, 6, 1] (step99o237MatrixCodeNat M) hbool
  rwa [step99o237_codeMat_matrixCode] at hspan

private theorem step99o237s8_QtInv :
    (codeMat 442 : Mat3).transpose⁻¹ = (codeMat 334 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 442 : Mat3).transpose * (codeMat 334 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o237s8_targetSpan_le_action :
    step99o237ActualSource8 ≤ actionW (codeMat 489) (codeMat 442) o56W := by
  apply step99o237_spanCodes_le_of_gens [266, 136, 96, 18, 6, 1]
    (actionW (codeMat 489) (codeMat 442) o56W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 161 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 161 (by decide)
    have hact : actionA (codeMat 489) (codeMat 442) (codeMat 161) = codeMat 266 := by
      unfold actionA
      rw [step99o237s8_QtInv]
      show (codeMat 489 : Mat3).transpose * codeMat 161 * (codeMat 334 : Mat3).transpose = codeMat 266
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 175 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 175 (by decide)
    have hact : actionA (codeMat 489) (codeMat 442) (codeMat 175) = codeMat 136 := by
      unfold actionA
      rw [step99o237s8_QtInv]
      show (codeMat 489 : Mat3).transpose * codeMat 175 * (codeMat 334 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 418 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 418 (by decide)
    have hact : actionA (codeMat 489) (codeMat 442) (codeMat 418) = codeMat 96 := by
      unfold actionA
      rw [step99o237s8_QtInv]
      show (codeMat 489 : Mat3).transpose * codeMat 418 * (codeMat 334 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 511 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 511 (by decide)
    have hact : actionA (codeMat 489) (codeMat 442) (codeMat 511) = codeMat 18 := by
      unfold actionA
      rw [step99o237s8_QtInv]
      show (codeMat 489 : Mat3).transpose * codeMat 511 * (codeMat 334 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 489) (codeMat 442) (codeMat 1) = codeMat 6 := by
      unfold actionA
      rw [step99o237s8_QtInv]
      show (codeMat 489 : Mat3).transpose * codeMat 1 * (codeMat 334 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 489) (codeMat 442) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step99o237s8_QtInv]
      show (codeMat 489 : Mat3).transpose * codeMat 2 * (codeMat 334 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact

theorem step99o237s8Dispatch :
    QuotientRankAtLeast (o237SourceU ⟨8, by omega⟩) 14 := by
  have hP : Invertible (codeMat 489 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 442 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 489) (codeMat 442) o56W) 14 :=
    @quotientRankAtLeast_action (codeMat 489) (codeMat 442) hP hQ o56W 14 step99_orbit56_lb14_unconditional
  have hMono : QuotientRankAtLeast step99o237ActualSource8 14 :=
    quotientRankAtLeast_mono step99o237s8_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o237s8_sourceU_le hMono

-- Source 9 (row 9): orbit 56, lb 14
def step99o237ActualSource9 : Submodule F2 Mat3 := spanCodes [258, 128, 96, 20, 8, 1]

private theorem step99o237s9_sourceU_le :
    (o237SourceU ⟨9, by omega⟩) ≤ step99o237ActualSource9 := by
  intro M hM
  have hbool : spanContainsCodeCore [258, 128, 96, 20, 8, 1] (step99o237MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 258) ⊓ kerEvalFunc (codeMat 96)) ⊓ kerEvalFunc (codeMat 20)) at hM
    change ((evalFunc (codeMat 258) M = 0 ∧ evalFunc (codeMat 96) M = 0) ∧ evalFunc (codeMat 20) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 128, 96, 20, 8, 1] (step99o237MatrixCodeNat M) hbool
  rwa [step99o237_codeMat_matrixCode] at hspan

private theorem step99o237s9_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o237s9_targetSpan_le_transposeAction :
    step99o237ActualSource9 ≤ transposeW (actionW (codeMat 161) (codeMat 266) o56W) := by
  apply step99o237_spanCodes_le_of_gens [258, 128, 96, 20, 8, 1]
    (transposeW (actionW (codeMat 161) (codeMat 266) o56W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    -- g=258, g^T=264; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 160 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 160) = codeMat 264 := by
      unfold actionA
      rw [step99o237s9_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * (codeMat 266 : Mat3).transpose = codeMat 264
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 264 ∈ actionW (codeMat 161) (codeMat 266) o56W :=
      step99o237_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 264 : Mat3).transpose = codeMat 258 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h1
    -- g=128, g^T=32; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 256 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 256) = codeMat 32 := by
      unfold actionA
      rw [step99o237s9_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 256 * (codeMat 266 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 32 ∈ actionW (codeMat 161) (codeMat 266) o56W :=
      step99o237_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 32 : Mat3).transpose = codeMat 128 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h2
    -- g=96, g^T=132; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 12 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 12 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 12) = codeMat 132 := by
      unfold actionA
      rw [step99o237s9_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 12 * (codeMat 266 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 132 ∈ actionW (codeMat 161) (codeMat 266) o56W :=
      step99o237_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 132 : Mat3).transpose = codeMat 96 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h3
    -- g=20, g^T=80; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 80 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 80 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 80) = codeMat 80 := by
      unfold actionA
      rw [step99o237s9_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 80 * (codeMat 266 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 80 ∈ actionW (codeMat 161) (codeMat 266) o56W :=
      step99o237_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 80 : Mat3).transpose = codeMat 20 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h4
    -- g=8, g^T=2; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 1 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 1) = codeMat 2 := by
      unfold actionA
      rw [step99o237s9_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 2 ∈ actionW (codeMat 161) (codeMat 266) o56W :=
      step99o237_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 2 : Mat3).transpose = codeMat 8 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h5
    -- g=1, g^T=1; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 2 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step99o237s9_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 1 ∈ actionW (codeMat 161) (codeMat 266) o56W :=
      step99o237_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 1 : Mat3).transpose = codeMat 1 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_transposeW_of_witness hmemAction htrans

theorem step99o237s9Dispatch :
    QuotientRankAtLeast (o237SourceU ⟨9, by omega⟩) 14 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 266) o56W) 14 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 266) hP hQ o56W 14 step99_orbit56_lb14_unconditional
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 161) (codeMat 266) o56W)) 14 :=
    quotientRankAtLeast_transpose hAct
  have hMono : QuotientRankAtLeast step99o237ActualSource9 14 :=
    quotientRankAtLeast_mono step99o237s9_targetSpan_le_transposeAction hT
  exact quotientRankAtLeast_mono step99o237s9_sourceU_le hMono

-- Source 10 (row 10): orbit 68, lb 14
def step99o237ActualSource10 : Submodule F2 Mat3 := spanCodes [260, 134, 96, 20, 14, 1]

private theorem step99o237s10_sourceU_le :
    (o237SourceU ⟨10, by omega⟩) ≤ step99o237ActualSource10 := by
  intro M hM
  have hbool : spanContainsCodeCore [260, 134, 96, 20, 14, 1] (step99o237MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 258 + codeMat 20) ⊓ kerEvalFunc (codeMat 138)) ⊓ kerEvalFunc (codeMat 96)) at hM
    change ((evalFunc (codeMat 258 + codeMat 20) M = 0 ∧ evalFunc (codeMat 138) M = 0) ∧ evalFunc (codeMat 96) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 134, 96, 20, 14, 1] (step99o237MatrixCodeNat M) hbool
  rwa [step99o237_codeMat_matrixCode] at hspan

private theorem step99o237s10_QtInv :
    (codeMat 205 : Mat3).transpose⁻¹ = (codeMat 242 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 205 : Mat3).transpose * (codeMat 242 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o237s10_targetSpan_le_action :
    step99o237ActualSource10 ≤ actionW (codeMat 117) (codeMat 205) o68W := by
  apply step99o237_spanCodes_le_of_gens [260, 134, 96, 20, 14, 1]
    (actionW (codeMat 117) (codeMat 205) o68W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 1 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 117) (codeMat 205) (codeMat 1) = codeMat 260 := by
      unfold actionA
      rw [step99o237s10_QtInv]
      show (codeMat 117 : Mat3).transpose * codeMat 1 * (codeMat 242 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 68 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 117) (codeMat 205) (codeMat 68) = codeMat 134 := by
      unfold actionA
      rw [step99o237s10_QtInv]
      show (codeMat 117 : Mat3).transpose * codeMat 68 * (codeMat 242 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 398 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 398 (by decide)
    have hact : actionA (codeMat 117) (codeMat 205) (codeMat 398) = codeMat 96 := by
      unfold actionA
      rw [step99o237s10_QtInv]
      show (codeMat 117 : Mat3).transpose * codeMat 398 * (codeMat 242 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 356 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 356 (by decide)
    have hact : actionA (codeMat 117) (codeMat 205) (codeMat 356) = codeMat 20 := by
      unfold actionA
      rw [step99o237s10_QtInv]
      show (codeMat 117 : Mat3).transpose * codeMat 356 * (codeMat 242 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 191 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 191 (by decide)
    have hact : actionA (codeMat 117) (codeMat 205) (codeMat 191) = codeMat 14 := by
      unfold actionA
      rw [step99o237s10_QtInv]
      show (codeMat 117 : Mat3).transpose * codeMat 191 * (codeMat 242 : Mat3).transpose = codeMat 14
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 448 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 448 (by decide)
    have hact : actionA (codeMat 117) (codeMat 205) (codeMat 448) = codeMat 1 := by
      unfold actionA
      rw [step99o237s10_QtInv]
      show (codeMat 117 : Mat3).transpose * codeMat 448 * (codeMat 242 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact

theorem step99o237s10Dispatch :
    QuotientRankAtLeast (o237SourceU ⟨10, by omega⟩) 14 := by
  have hP : Invertible (codeMat 117 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 205 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 117) (codeMat 205) o68W) 14 :=
    @quotientRankAtLeast_action (codeMat 117) (codeMat 205) hP hQ o68W 14 step99_orbit68_lb14_unconditional
  have hMono : QuotientRankAtLeast step99o237ActualSource10 14 :=
    quotientRankAtLeast_mono step99o237s10_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o237s10_sourceU_le hMono

-- Source 11 (row 11): orbit 56, lb 14
def step99o237ActualSource11 : Submodule F2 Mat3 := spanCodes [266, 136, 64, 32, 20, 1]

private theorem step99o237s11_sourceU_le :
    (o237SourceU ⟨11, by omega⟩) ≤ step99o237ActualSource11 := by
  intro M hM
  have hbool : spanContainsCodeCore [266, 136, 64, 32, 20, 1] (step99o237MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 258) ⊓ kerEvalFunc (codeMat 138)) ⊓ kerEvalFunc (codeMat 20)) at hM
    change ((evalFunc (codeMat 258) M = 0 ∧ evalFunc (codeMat 138) M = 0) ∧ evalFunc (codeMat 20) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [266, 136, 64, 32, 20, 1] (step99o237MatrixCodeNat M) hbool
  rwa [step99o237_codeMat_matrixCode] at hspan

private theorem step99o237s11_QtInv :
    (codeMat 158 : Mat3).transpose⁻¹ = (codeMat 358 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 158 : Mat3).transpose * (codeMat 358 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o237s11_targetSpan_le_transposeAction :
    step99o237ActualSource11 ≤ transposeW (actionW (codeMat 409) (codeMat 158) o56W) := by
  apply step99o237_spanCodes_le_of_gens [266, 136, 64, 32, 20, 1]
    (transposeW (actionW (codeMat 409) (codeMat 158) o56W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    -- g=266, g^T=266; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 92 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 92 (by decide)
    have hact : actionA (codeMat 409) (codeMat 158) (codeMat 92) = codeMat 266 := by
      unfold actionA
      rw [step99o237s11_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 92 * (codeMat 358 : Mat3).transpose = codeMat 266
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 266 ∈ actionW (codeMat 409) (codeMat 158) o56W :=
      step99o237_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 266 : Mat3).transpose = codeMat 266 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h1
    -- g=136, g^T=34; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 14 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 14 (by decide)
    have hact : actionA (codeMat 409) (codeMat 158) (codeMat 14) = codeMat 34 := by
      unfold actionA
      rw [step99o237s11_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 14 * (codeMat 358 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 34 ∈ actionW (codeMat 409) (codeMat 158) o56W :=
      step99o237_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 34 : Mat3).transpose = codeMat 136 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h2
    -- g=64, g^T=4; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 1 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 409) (codeMat 158) (codeMat 1) = codeMat 4 := by
      unfold actionA
      rw [step99o237s11_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 1 * (codeMat 358 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 4 ∈ actionW (codeMat 409) (codeMat 158) o56W :=
      step99o237_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 4 : Mat3).transpose = codeMat 64 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h3
    -- g=32, g^T=128; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 511 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 511 (by decide)
    have hact : actionA (codeMat 409) (codeMat 158) (codeMat 511) = codeMat 128 := by
      unfold actionA
      rw [step99o237s11_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 511 * (codeMat 358 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 128 ∈ actionW (codeMat 409) (codeMat 158) o56W :=
      step99o237_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 128 : Mat3).transpose = codeMat 32 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h4
    -- g=20, g^T=80; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 173 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 173 (by decide)
    have hact : actionA (codeMat 409) (codeMat 158) (codeMat 173) = codeMat 80 := by
      unfold actionA
      rw [step99o237s11_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 173 * (codeMat 358 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 80 ∈ actionW (codeMat 409) (codeMat 158) o56W :=
      step99o237_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 80 : Mat3).transpose = codeMat 20 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h5
    -- g=1, g^T=1; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 2 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 409) (codeMat 158) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step99o237s11_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 2 * (codeMat 358 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 1 ∈ actionW (codeMat 409) (codeMat 158) o56W :=
      step99o237_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 1 : Mat3).transpose = codeMat 1 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_transposeW_of_witness hmemAction htrans

theorem step99o237s11Dispatch :
    QuotientRankAtLeast (o237SourceU ⟨11, by omega⟩) 14 := by
  have hP : Invertible (codeMat 409 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 158 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 409) (codeMat 158) o56W) 14 :=
    @quotientRankAtLeast_action (codeMat 409) (codeMat 158) hP hQ o56W 14 step99_orbit56_lb14_unconditional
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 409) (codeMat 158) o56W)) 14 :=
    quotientRankAtLeast_transpose hAct
  have hMono : QuotientRankAtLeast step99o237ActualSource11 14 :=
    quotientRankAtLeast_mono step99o237s11_targetSpan_le_transposeAction hT
  exact quotientRankAtLeast_mono step99o237s11_sourceU_le hMono

-- Source 12 (row 12): orbit 68, lb 14
def step99o237ActualSource12 : Submodule F2 Mat3 := spanCodes [266, 136, 68, 36, 20, 1]

private theorem step99o237s12_sourceU_le :
    (o237SourceU ⟨12, by omega⟩) ≤ step99o237ActualSource12 := by
  intro M hM
  have hbool : spanContainsCodeCore [266, 136, 68, 36, 20, 1] (step99o237MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 258) ⊓ kerEvalFunc (codeMat 138)) ⊓ kerEvalFunc (codeMat 96 + codeMat 20)) at hM
    change ((evalFunc (codeMat 258) M = 0 ∧ evalFunc (codeMat 138) M = 0) ∧ evalFunc (codeMat 96 + codeMat 20) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [266, 136, 68, 36, 20, 1] (step99o237MatrixCodeNat M) hbool
  rwa [step99o237_codeMat_matrixCode] at hspan

private theorem step99o237s12_QtInv :
    (codeMat 226 : Mat3).transpose⁻¹ = (codeMat 141 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 226 : Mat3).transpose * (codeMat 141 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o237s12_targetSpan_le_action :
    step99o237ActualSource12 ≤ actionW (codeMat 158) (codeMat 226) o68W := by
  apply step99o237_spanCodes_le_of_gens [266, 136, 68, 36, 20, 1]
    (actionW (codeMat 158) (codeMat 226) o68W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 234 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 234 (by decide)
    have hact : actionA (codeMat 158) (codeMat 226) (codeMat 234) = codeMat 266 := by
      unfold actionA
      rw [step99o237s12_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 234 * (codeMat 141 : Mat3).transpose = codeMat 266
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 69 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 69 (by decide)
    have hact : actionA (codeMat 158) (codeMat 226) (codeMat 69) = codeMat 136 := by
      unfold actionA
      rw [step99o237s12_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 69 * (codeMat 141 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 404 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 404 (by decide)
    have hact : actionA (codeMat 158) (codeMat 226) (codeMat 404) = codeMat 68 := by
      unfold actionA
      rw [step99o237s12_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 404 * (codeMat 141 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 16 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 158) (codeMat 226) (codeMat 16) = codeMat 36 := by
      unfold actionA
      rw [step99o237s12_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 16 * (codeMat 141 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 464 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 464 (by decide)
    have hact : actionA (codeMat 158) (codeMat 226) (codeMat 464) = codeMat 20 := by
      unfold actionA
      rw [step99o237s12_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 464 * (codeMat 141 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 288 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 288 (by decide)
    have hact : actionA (codeMat 158) (codeMat 226) (codeMat 288) = codeMat 1 := by
      unfold actionA
      rw [step99o237s12_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 288 * (codeMat 141 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact

theorem step99o237s12Dispatch :
    QuotientRankAtLeast (o237SourceU ⟨12, by omega⟩) 14 := by
  have hP : Invertible (codeMat 158 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 226 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 158) (codeMat 226) o68W) 14 :=
    @quotientRankAtLeast_action (codeMat 158) (codeMat 226) hP hQ o68W 14 step99_orbit68_lb14_unconditional
  have hMono : QuotientRankAtLeast step99o237ActualSource12 14 :=
    quotientRankAtLeast_mono step99o237s12_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o237s12_sourceU_le hMono

-- Source 13 (row 13): orbit 56, lb 14
def step99o237ActualSource13 : Submodule F2 Mat3 := spanCodes [266, 136, 72, 40, 20, 1]

private theorem step99o237s13_sourceU_le :
    (o237SourceU ⟨13, by omega⟩) ≤ step99o237ActualSource13 := by
  intro M hM
  have hbool : spanContainsCodeCore [266, 136, 72, 40, 20, 1] (step99o237MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 258) ⊓ kerEvalFunc (codeMat 138 + codeMat 96)) ⊓ kerEvalFunc (codeMat 20)) at hM
    change ((evalFunc (codeMat 258) M = 0 ∧ evalFunc (codeMat 138 + codeMat 96) M = 0) ∧ evalFunc (codeMat 20) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [266, 136, 72, 40, 20, 1] (step99o237MatrixCodeNat M) hbool
  rwa [step99o237_codeMat_matrixCode] at hspan

private theorem step99o237s13_QtInv :
    (codeMat 428 : Mat3).transpose⁻¹ = (codeMat 107 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 428 : Mat3).transpose * (codeMat 107 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o237s13_targetSpan_le_transposeAction :
    step99o237ActualSource13 ≤ transposeW (actionW (codeMat 377) (codeMat 428) o56W) := by
  apply step99o237_spanCodes_le_of_gens [266, 136, 72, 40, 20, 1]
    (transposeW (actionW (codeMat 377) (codeMat 428) o56W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    -- g=266, g^T=266; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 339 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 339 (by decide)
    have hact : actionA (codeMat 377) (codeMat 428) (codeMat 339) = codeMat 266 := by
      unfold actionA
      rw [step99o237s13_QtInv]
      show (codeMat 377 : Mat3).transpose * codeMat 339 * (codeMat 107 : Mat3).transpose = codeMat 266
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 266 ∈ actionW (codeMat 377) (codeMat 428) o56W :=
      step99o237_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 266 : Mat3).transpose = codeMat 266 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h1
    -- g=136, g^T=34; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 508 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 508 (by decide)
    have hact : actionA (codeMat 377) (codeMat 428) (codeMat 508) = codeMat 34 := by
      unfold actionA
      rw [step99o237s13_QtInv]
      show (codeMat 377 : Mat3).transpose * codeMat 508 * (codeMat 107 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 34 ∈ actionW (codeMat 377) (codeMat 428) o56W :=
      step99o237_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 34 : Mat3).transpose = codeMat 136 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h2
    -- g=72, g^T=6; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 3 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 377) (codeMat 428) (codeMat 3) = codeMat 6 := by
      unfold actionA
      rw [step99o237s13_QtInv]
      show (codeMat 377 : Mat3).transpose * codeMat 3 * (codeMat 107 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 6 ∈ actionW (codeMat 377) (codeMat 428) o56W :=
      step99o237_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 6 : Mat3).transpose = codeMat 72 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h3
    -- g=40, g^T=130; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 256 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 377) (codeMat 428) (codeMat 256) = codeMat 130 := by
      unfold actionA
      rw [step99o237s13_QtInv]
      show (codeMat 377 : Mat3).transpose * codeMat 256 * (codeMat 107 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 130 ∈ actionW (codeMat 377) (codeMat 428) o56W :=
      step99o237_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 130 : Mat3).transpose = codeMat 40 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h4
    -- g=20, g^T=80; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 418 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 418 (by decide)
    have hact : actionA (codeMat 377) (codeMat 428) (codeMat 418) = codeMat 80 := by
      unfold actionA
      rw [step99o237s13_QtInv]
      show (codeMat 377 : Mat3).transpose * codeMat 418 * (codeMat 107 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 80 ∈ actionW (codeMat 377) (codeMat 428) o56W :=
      step99o237_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 80 : Mat3).transpose = codeMat 20 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h5
    -- g=1, g^T=1; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 2 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 377) (codeMat 428) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step99o237s13_QtInv]
      show (codeMat 377 : Mat3).transpose * codeMat 2 * (codeMat 107 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 1 ∈ actionW (codeMat 377) (codeMat 428) o56W :=
      step99o237_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 1 : Mat3).transpose = codeMat 1 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_transposeW_of_witness hmemAction htrans

theorem step99o237s13Dispatch :
    QuotientRankAtLeast (o237SourceU ⟨13, by omega⟩) 14 := by
  have hP : Invertible (codeMat 377 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 428 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 377) (codeMat 428) o56W) 14 :=
    @quotientRankAtLeast_action (codeMat 377) (codeMat 428) hP hQ o56W 14 step99_orbit56_lb14_unconditional
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 377) (codeMat 428) o56W)) 14 :=
    quotientRankAtLeast_transpose hAct
  have hMono : QuotientRankAtLeast step99o237ActualSource13 14 :=
    quotientRankAtLeast_mono step99o237s13_targetSpan_le_transposeAction hT
  exact quotientRankAtLeast_mono step99o237s13_sourceU_le hMono

-- Source 14 (row 14): orbit 68, lb 14
def step99o237ActualSource14 : Submodule F2 Mat3 := spanCodes [266, 136, 74, 42, 20, 1]

private theorem step99o237s14_sourceU_le :
    (o237SourceU ⟨14, by omega⟩) ≤ step99o237ActualSource14 := by
  intro M hM
  have hbool : spanContainsCodeCore [266, 136, 74, 42, 20, 1] (step99o237MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 258 + codeMat 96) ⊓ kerEvalFunc (codeMat 138)) ⊓ kerEvalFunc (codeMat 20)) at hM
    change ((evalFunc (codeMat 258 + codeMat 96) M = 0 ∧ evalFunc (codeMat 138) M = 0) ∧ evalFunc (codeMat 20) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [266, 136, 74, 42, 20, 1] (step99o237MatrixCodeNat M) hbool
  rwa [step99o237_codeMat_matrixCode] at hspan

private theorem step99o237s14_QtInv :
    (codeMat 244 : Mat3).transpose⁻¹ = (codeMat 95 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 244 : Mat3).transpose * (codeMat 95 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o237s14_targetSpan_le_action :
    step99o237ActualSource14 ≤ actionW (codeMat 299) (codeMat 244) o68W := by
  apply step99o237_spanCodes_le_of_gens [266, 136, 74, 42, 20, 1]
    (actionW (codeMat 299) (codeMat 244) o68W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 84 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 84 (by decide)
    have hact : actionA (codeMat 299) (codeMat 244) (codeMat 84) = codeMat 266 := by
      unfold actionA
      rw [step99o237s14_QtInv]
      show (codeMat 299 : Mat3).transpose * codeMat 84 * (codeMat 95 : Mat3).transpose = codeMat 266
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 164 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 164 (by decide)
    have hact : actionA (codeMat 299) (codeMat 244) (codeMat 164) = codeMat 136 := by
      unfold actionA
      rw [step99o237s14_QtInv]
      show (codeMat 299 : Mat3).transpose * codeMat 164 * (codeMat 95 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 404 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 404 (by decide)
    have hact : actionA (codeMat 299) (codeMat 244) (codeMat 404) = codeMat 74 := by
      unfold actionA
      rw [step99o237s14_QtInv]
      show (codeMat 299 : Mat3).transpose * codeMat 404 * (codeMat 95 : Mat3).transpose = codeMat 74
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 79 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 79 (by decide)
    have hact : actionA (codeMat 299) (codeMat 244) (codeMat 79) = codeMat 42 := by
      unfold actionA
      rw [step99o237s14_QtInv]
      show (codeMat 299 : Mat3).transpose * codeMat 79 * (codeMat 95 : Mat3).transpose = codeMat 42
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 366 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 366 (by decide)
    have hact : actionA (codeMat 299) (codeMat 244) (codeMat 366) = codeMat 20 := by
      unfold actionA
      rw [step99o237s14_QtInv]
      show (codeMat 299 : Mat3).transpose * codeMat 366 * (codeMat 95 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 288 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 288 (by decide)
    have hact : actionA (codeMat 299) (codeMat 244) (codeMat 288) = codeMat 1 := by
      unfold actionA
      rw [step99o237s14_QtInv]
      show (codeMat 299 : Mat3).transpose * codeMat 288 * (codeMat 95 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o237_codeMat_mem_actionW_of_witness hw hact

theorem step99o237s14Dispatch :
    QuotientRankAtLeast (o237SourceU ⟨14, by omega⟩) 14 := by
  have hP : Invertible (codeMat 299 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 244 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 299) (codeMat 244) o68W) 14 :=
    @quotientRankAtLeast_action (codeMat 299) (codeMat 244) hP hQ o68W 14 step99_orbit68_lb14_unconditional
  have hMono : QuotientRankAtLeast step99o237ActualSource14 14 :=
    quotientRankAtLeast_mono step99o237s14_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o237s14_sourceU_le hMono

theorem step99o237_all_dispatch (i : Fin 15) :
    QuotientRankAtLeast (o237SourceU i) (o237SourceLb i) := by
  fin_cases i
  · exact step99o237s0Dispatch
  · exact step99o237s1Dispatch
  · exact step99o237s2Dispatch
  · exact step99o237s3Dispatch
  · exact step99o237s4Dispatch
  · exact step99o237s5Dispatch
  · exact step99o237s6Dispatch
  · exact step99o237s7Dispatch
  · exact step99o237s8Dispatch
  · exact step99o237s9Dispatch
  · exact step99o237s10Dispatch
  · exact step99o237s11Dispatch
  · exact step99o237s12Dispatch
  · exact step99o237s13Dispatch
  · exact step99o237s14Dispatch

theorem step99_orbit237_lb16_unconditional :
    QuotientRankAtLeast o237W 16 :=
  o237Lb16 step99o237_all_dispatch

end QiushiMatmul
