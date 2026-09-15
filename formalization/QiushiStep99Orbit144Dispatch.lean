import QiushiCodeSpanCore
import QiushiFlattenSeeds
import QiushiMonotonicity
import QiushiOrbit10FP
import QiushiOrbit14FP
import QiushiOrbitTransport
import QiushiStep98Orbit144Consumer
import QiushiTransposeTransport

set_option maxHeartbeats 800000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem step99o144_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step99o144MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step99o144_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step99o144MatrixCodeNat M) = M := by decide

lemma step99o144_codeMat_matrixCode (M : Mat3) :
    codeMat (step99o144MatrixCodeNat M) = M :=
  step99o144_codeMat_matrixCode_all M

private theorem step99o144_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step99o144_linearCombination_mem (bs : List Nat) {n : Nat}
    (b : Fin n → Nat) (c : Fin n → F2) (hb : ∀ i, b i ∈ bs) :
    (∑ i, c i • codeMat (b i)) ∈ spanCodes bs := by
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b i, hb i, rfl⟩)

private theorem step99o144_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

private theorem step99o144_codeMat_mem_transposeW_of_witness
    {V : Submodule F2 Mat3} {pre tpre : Nat}
    (h_mem : codeMat tpre ∈ V)
    (h_trans : (codeMat tpre : Mat3).transpose = codeMat pre) :
    codeMat pre ∈ transposeW V := by
  change ∃ X, X ∈ V ∧ transposeLinearMap X = codeMat pre
  exact ⟨codeMat tpre, h_mem, h_trans⟩

-- Source 0 (row 15): orbit 10, lb 12
def step99o144ActualSource0 : Submodule F2 Mat3 := spanCodes [264, 140, 72, 32, 28, 2, 1]

private theorem step99o144s0_sourceU_le :
    (o144SourceU ⟨0, by omega⟩) ≤ step99o144ActualSource0 := by
  intro M hM
  change evalFunc (codeMat 264 + codeMat 68) M = 0 ∧
    evalFunc (codeMat 136 + codeMat 28) M = 0 at hM
  norm_num [evalFunc, Fin.sum_univ_succ, codeMat, Nat.testBit_eq_decide_div_mod_eq] at hM
  let b : Fin 7 → Nat := ![264, 140, 72, 32, 28, 2, 1]
  -- The seven pivot entries are coefficients; the two kernel equations recover the others.
  let c : Fin 7 → F2 := ![M 2 2, M 2 1, M 2 0, M 1 2, M 1 1, M 0 1, M 0 0]
  have hrec : M = ∑ i, c i • codeMat (b i) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [b, c, Fin.sum_univ_succ, codeMat, Nat.testBit_eq_decide_div_mod_eq] <;>
      first
      | rfl
      | solve | linear_combination (norm := (ring_nf; simp [show (2 : F2) = 0 by decide])) hM.1
      | solve | linear_combination (norm := (ring_nf; simp [show (2 : F2) = 0 by decide])) hM.2
      | solve | linear_combination (norm := (ring_nf; simp [show (2 : F2) = 0 by decide])) hM.1 + hM.2
  rw [hrec]
  exact step99o144_linearCombination_mem _ b c (by intro i; fin_cases i <;> decide)

private theorem step99o144s0_QtInv :
    (codeMat 279 : Mat3).transpose⁻¹ = (codeMat 279 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 279 : Mat3).transpose * (codeMat 279 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o144s0_targetSpan_le_action :
    step99o144ActualSource0 ≤ actionW (codeMat 270) (codeMat 279) orbit10W := by
  apply step99o144_spanCodes_le_of_gens [264, 140, 72, 32, 28, 2, 1]
    (actionW (codeMat 270) (codeMat 279) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 257 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 257 (by decide)
    have hact : actionA (codeMat 270) (codeMat 279) (codeMat 257) = codeMat 264 := by
      unfold actionA
      rw [step99o144s0_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 257 * (codeMat 279 : Mat3).transpose = codeMat 264
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o144_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 169 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 169 (by decide)
    have hact : actionA (codeMat 270) (codeMat 279) (codeMat 169) = codeMat 140 := by
      unfold actionA
      rw [step99o144s0_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 169 * (codeMat 279 : Mat3).transpose = codeMat 140
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o144_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 270) (codeMat 279) (codeMat 1) = codeMat 72 := by
      unfold actionA
      rw [step99o144s0_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 1 * (codeMat 279 : Mat3).transpose = codeMat 72
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o144_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 325 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 325 (by decide)
    have hact : actionA (codeMat 270) (codeMat 279) (codeMat 325) = codeMat 32 := by
      unfold actionA
      rw [step99o144s0_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 325 * (codeMat 279 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o144_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 170 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 170 (by decide)
    have hact : actionA (codeMat 270) (codeMat 279) (codeMat 170) = codeMat 28 := by
      unfold actionA
      rw [step99o144s0_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 170 * (codeMat 279 : Mat3).transpose = codeMat 28
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o144_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 24 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide)
    have hact : actionA (codeMat 270) (codeMat 279) (codeMat 24) = codeMat 2 := by
      unfold actionA
      rw [step99o144s0_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 24 * (codeMat 279 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o144_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 270) (codeMat 279) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step99o144s0_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 8 * (codeMat 279 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o144_codeMat_mem_actionW_of_witness hw hact

theorem step99o144s0Dispatch :
    QuotientRankAtLeast (o144SourceU ⟨0, by omega⟩) 12 := by
  have hP : Invertible (codeMat 270 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 279 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 270) (codeMat 279) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 270) (codeMat 279) hP hQ orbit10W 12 orbit10_lb12
  have hMono : QuotientRankAtLeast step99o144ActualSource0 12 :=
    quotientRankAtLeast_mono step99o144s0_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o144s0_sourceU_le hMono

-- Source 1 (row 16): orbit 10, lb 12
def step99o144ActualSource1 : Submodule F2 Mat3 := spanCodes [268, 128, 64, 32, 20, 2, 1]

private theorem step99o144s1_sourceU_le :
    (o144SourceU ⟨1, by omega⟩) ≤ step99o144ActualSource1 := by
  intro M hM
  change evalFunc (codeMat 264) M = 0 ∧ evalFunc (codeMat 28) M = 0 at hM
  norm_num [evalFunc, Fin.sum_univ_succ, codeMat, Nat.testBit_eq_decide_div_mod_eq] at hM
  let b : Fin 7 → Nat := ![268, 128, 64, 32, 20, 2, 1]
  let c : Fin 7 → F2 := ![M 2 2, M 2 1, M 2 0, M 1 2, M 1 1, M 0 1, M 0 0]
  have hrec : M = ∑ i, c i • codeMat (b i) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [b, c, Fin.sum_univ_succ, codeMat, Nat.testBit_eq_decide_div_mod_eq] <;>
      first
      | rfl
      | solve | linear_combination (norm := (ring_nf; simp [show (2 : F2) = 0 by decide])) hM.1
      | solve | linear_combination (norm := (ring_nf; simp [show (2 : F2) = 0 by decide])) hM.2
      | solve | linear_combination (norm := (ring_nf; simp [show (2 : F2) = 0 by decide])) hM.1 + hM.2
  rw [hrec]
  exact step99o144_linearCombination_mem _ b c (by intro i; fin_cases i <;> decide)

private theorem step99o144s1_QtInv :
    (codeMat 281 : Mat3).transpose⁻¹ = (codeMat 281 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 281 : Mat3).transpose * (codeMat 281 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o144s1_targetSpan_le_action :
    step99o144ActualSource1 ≤ actionW (codeMat 140) (codeMat 281) orbit10W := by
  apply step99o144_spanCodes_le_of_gens [268, 128, 64, 32, 20, 2, 1]
    (actionW (codeMat 140) (codeMat 281) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 228 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 228 (by decide)
    have hact : actionA (codeMat 140) (codeMat 281) (codeMat 228) = codeMat 268 := by
      unfold actionA
      rw [step99o144s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 228 * (codeMat 281 : Mat3).transpose = codeMat 268
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o144_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 140) (codeMat 281) (codeMat 2) = codeMat 128 := by
      unfold actionA
      rw [step99o144s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 2 * (codeMat 281 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o144_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 3 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 3 (by decide)
    have hact : actionA (codeMat 140) (codeMat 281) (codeMat 3) = codeMat 64 := by
      unfold actionA
      rw [step99o144s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 3 * (codeMat 281 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o144_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 140) (codeMat 281) (codeMat 256) = codeMat 32 := by
      unfold actionA
      rw [step99o144s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 256 * (codeMat 281 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o144_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 140) (codeMat 281) (codeMat 160) = codeMat 20 := by
      unfold actionA
      rw [step99o144s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 160 * (codeMat 281 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o144_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 140) (codeMat 281) (codeMat 16) = codeMat 2 := by
      unfold actionA
      rw [step99o144s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 16 * (codeMat 281 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o144_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 24 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide)
    have hact : actionA (codeMat 140) (codeMat 281) (codeMat 24) = codeMat 1 := by
      unfold actionA
      rw [step99o144s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 24 * (codeMat 281 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o144_codeMat_mem_actionW_of_witness hw hact

theorem step99o144s1Dispatch :
    QuotientRankAtLeast (o144SourceU ⟨1, by omega⟩) 12 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 281 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 281) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 281) hP hQ orbit10W 12 orbit10_lb12
  have hMono : QuotientRankAtLeast step99o144ActualSource1 12 :=
    quotientRankAtLeast_mono step99o144s1_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o144s1_sourceU_le hMono

-- Source 2 (row 21): orbit 14, lb 12
def step99o144ActualSource2 : Submodule F2 Mat3 := spanCodes [256, 136, 68, 32, 16, 2, 1]

private theorem step99o144s2_sourceU_le :
    (o144SourceU ⟨2, by omega⟩) ≤ step99o144ActualSource2 := by
  intro M hM
  change evalFunc (codeMat 136) M = 0 ∧ evalFunc (codeMat 68) M = 0 at hM
  norm_num [evalFunc, Fin.sum_univ_succ, codeMat, Nat.testBit_eq_decide_div_mod_eq] at hM
  let b : Fin 7 → Nat := ![256, 136, 68, 32, 16, 2, 1]
  let c : Fin 7 → F2 := ![M 2 2, M 2 1, M 2 0, M 1 2, M 1 1, M 0 1, M 0 0]
  have hrec : M = ∑ i, c i • codeMat (b i) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [b, c, Fin.sum_univ_succ, codeMat, Nat.testBit_eq_decide_div_mod_eq] <;>
      first
      | rfl
      | solve | linear_combination (norm := (ring_nf; simp [show (2 : F2) = 0 by decide])) hM.1
      | solve | linear_combination (norm := (ring_nf; simp [show (2 : F2) = 0 by decide])) hM.2
  rw [hrec]
  exact step99o144_linearCombination_mem _ b c (by intro i; fin_cases i <;> decide)

private theorem step99o144s2_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o144s2_targetSpan_le_action :
    step99o144ActualSource2 ≤ actionW (codeMat 98) (codeMat 84) orbit14W := by
  apply step99o144_spanCodes_le_of_gens [256, 136, 68, 32, 16, 2, 1]
    (actionW (codeMat 98) (codeMat 84) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 98) (codeMat 84) (codeMat 8) = codeMat 256 := by
      unfold actionA
      rw [step99o144s2_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 8 * (codeMat 84 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o144_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 20 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 20 (by decide)
    have hact : actionA (codeMat 98) (codeMat 84) (codeMat 20) = codeMat 136 := by
      unfold actionA
      rw [step99o144s2_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 20 * (codeMat 84 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o144_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 98) (codeMat 84) (codeMat 96) = codeMat 68 := by
      unfold actionA
      rw [step99o144s2_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 96 * (codeMat 84 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o144_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 98) (codeMat 84) (codeMat 1) = codeMat 32 := by
      unfold actionA
      rw [step99o144s2_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 1 * (codeMat 84 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o144_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 98) (codeMat 84) (codeMat 2) = codeMat 16 := by
      unfold actionA
      rw [step99o144s2_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 2 * (codeMat 84 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o144_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 98) (codeMat 84) (codeMat 128) = codeMat 2 := by
      unfold actionA
      rw [step99o144s2_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 128 * (codeMat 84 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o144_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 98) (codeMat 84) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step99o144s2_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 256 * (codeMat 84 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o144_codeMat_mem_actionW_of_witness hw hact

theorem step99o144s2Dispatch :
    QuotientRankAtLeast (o144SourceU ⟨2, by omega⟩) 12 := by
  have hP : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 98) (codeMat 84) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 98) (codeMat 84) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step99o144ActualSource2 12 :=
    quotientRankAtLeast_mono step99o144s2_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o144s2_sourceU_le hMono

-- Source 3 (row 24): orbit 14, lb 12
def step99o144ActualSource3 : Submodule F2 Mat3 := spanCodes [260, 132, 76, 32, 24, 2, 1]

private theorem step99o144s3_sourceU_le :
    (o144SourceU ⟨3, by omega⟩) ≤ step99o144ActualSource3 := by
  intro M hM
  change evalFunc (codeMat 264 + codeMat 136 + codeMat 28) M = 0 ∧
    evalFunc (codeMat 68 + codeMat 28) M = 0 at hM
  norm_num [evalFunc, Fin.sum_univ_succ, codeMat, Nat.testBit_eq_decide_div_mod_eq] at hM
  let b : Fin 7 → Nat := ![260, 132, 76, 32, 24, 2, 1]
  let c : Fin 7 → F2 := ![M 2 2, M 2 1, M 2 0, M 1 2, M 1 1, M 0 1, M 0 0]
  have hrec : M = ∑ i, c i • codeMat (b i) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [b, c, Fin.sum_univ_succ, codeMat, Nat.testBit_eq_decide_div_mod_eq] <;>
      first
      | rfl
      | solve | linear_combination (norm := (ring_nf; simp [show (2 : F2) = 0 by decide])) hM.1
      | solve | linear_combination (norm := (ring_nf; simp [show (2 : F2) = 0 by decide])) hM.2
      | solve | linear_combination (norm := (ring_nf; simp [show (2 : F2) = 0 by decide,
          show (3 : F2) = 1 by decide, show (4 : F2) = 0 by decide])) hM.1 + hM.2
  rw [hrec]
  exact step99o144_linearCombination_mem _ b c (by intro i; fin_cases i <;> decide)

private theorem step99o144s3_QtInv :
    (codeMat 204 : Mat3).transpose⁻¹ = (codeMat 114 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 204 : Mat3).transpose * (codeMat 114 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o144s3_targetSpan_le_action :
    step99o144ActualSource3 ≤ actionW (codeMat 106) (codeMat 204) orbit14W := by
  apply step99o144_spanCodes_le_of_gens [260, 132, 76, 32, 24, 2, 1]
    (actionW (codeMat 106) (codeMat 204) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 106) (codeMat 204) (codeMat 8) = codeMat 260 := by
      unfold actionA
      rw [step99o144s3_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 8 * (codeMat 114 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o144_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 352 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 352 (by decide)
    have hact : actionA (codeMat 106) (codeMat 204) (codeMat 352) = codeMat 132 := by
      unfold actionA
      rw [step99o144s3_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 352 * (codeMat 114 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o144_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 502 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 502 (by decide)
    have hact : actionA (codeMat 106) (codeMat 204) (codeMat 502) = codeMat 76 := by
      unfold actionA
      rw [step99o144s3_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 502 * (codeMat 114 : Mat3).transpose = codeMat 76
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o144_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 106) (codeMat 204) (codeMat 1) = codeMat 32 := by
      unfold actionA
      rw [step99o144s3_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 1 * (codeMat 114 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o144_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 106) (codeMat 204) (codeMat 2) = codeMat 24 := by
      unfold actionA
      rw [step99o144s3_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 2 * (codeMat 114 : Mat3).transpose = codeMat 24
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o144_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 106) (codeMat 204) (codeMat 256) = codeMat 2 := by
      unfold actionA
      rw [step99o144s3_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 256 * (codeMat 114 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o144_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 106) (codeMat 204) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step99o144s3_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 384 * (codeMat 114 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o144_codeMat_mem_actionW_of_witness hw hact

theorem step99o144s3Dispatch :
    QuotientRankAtLeast (o144SourceU ⟨3, by omega⟩) 12 := by
  have hP : Invertible (codeMat 106 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 204 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 106) (codeMat 204) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 106) (codeMat 204) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step99o144ActualSource3 12 :=
    quotientRankAtLeast_mono step99o144s3_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o144s3_sourceU_le hMono

-- Source 4 (row 28): orbit 7, lb 9
def step99o144ActualSource4 : Submodule F2 Mat3 := spanCodes [400, 80, 32, 8, 4, 2, 1]

private theorem step99o144s4_sourceU_le :
    (o144SourceU ⟨4, by omega⟩) ≤ step99o144ActualSource4 := by
  intro M hM
  change evalFunc (codeMat 264 + codeMat 68 + codeMat 28) M = 0 ∧
    evalFunc (codeMat 136 + codeMat 68 + codeMat 28) M = 0 at hM
  norm_num [evalFunc, Fin.sum_univ_succ, codeMat, Nat.testBit_eq_decide_div_mod_eq] at hM
  let b : Fin 7 → Nat := ![400, 80, 32, 8, 4, 2, 1]
  let c : Fin 7 → F2 := ![M 2 2, M 2 0, M 1 2, M 1 0, M 0 2, M 0 1, M 0 0]
  have hrec : M = ∑ i, c i • codeMat (b i) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [b, c, Fin.sum_univ_succ, codeMat, Nat.testBit_eq_decide_div_mod_eq] <;>
      first
      | rfl
      | solve | linear_combination (norm := (ring_nf; simp [show (2 : F2) = 0 by decide])) hM.1
      | solve | linear_combination (norm := (ring_nf; simp [show (2 : F2) = 0 by decide])) hM.2
      | solve | linear_combination (norm := (ring_nf; simp [show (2 : F2) = 0 by decide,
          show (4 : F2) = 0 by decide])) hM.1 + hM.2
  rw [hrec]
  exact step99o144_linearCombination_mem _ b c (by intro i; fin_cases i <;> decide)

private theorem step99o144s4_QtInv :
    (codeMat 179 : Mat3).transpose⁻¹ = (codeMat 421 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 179 : Mat3).transpose * (codeMat 421 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o144s4_targetSpan_le_action :
    step99o144ActualSource4 ≤ actionW (codeMat 273) (codeMat 179) flatW_7 := by
  apply step99o144_spanCodes_le_of_gens [400, 80, 32, 8, 4, 2, 1]
    (actionW (codeMat 273) (codeMat 179) flatW_7)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 376 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 376 (by decide)
    have hact : actionA (codeMat 273) (codeMat 179) (codeMat 376) = codeMat 400 := by
      unfold actionA
      rw [step99o144s4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 376 * (codeMat 421 : Mat3).transpose = codeMat 400
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o144_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 120 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 120 (by decide)
    have hact : actionA (codeMat 273) (codeMat 179) (codeMat 120) = codeMat 80 := by
      unfold actionA
      rw [step99o144s4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 120 * (codeMat 421 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o144_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 16 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 16 (by decide)
    have hact : actionA (codeMat 273) (codeMat 179) (codeMat 16) = codeMat 32 := by
      unfold actionA
      rw [step99o144s4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 16 * (codeMat 421 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o144_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 179) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step99o144s4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 421 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o144_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 179) (codeMat 2) = codeMat 4 := by
      unfold actionA
      rw [step99o144s4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 421 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o144_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 7 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 7 (by decide)
    have hact : actionA (codeMat 273) (codeMat 179) (codeMat 7) = codeMat 2 := by
      unfold actionA
      rw [step99o144s4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 7 * (codeMat 421 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o144_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 1 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 179) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step99o144s4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 421 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o144_codeMat_mem_actionW_of_witness hw hact

theorem step99o144s4Dispatch :
    QuotientRankAtLeast (o144SourceU ⟨4, by omega⟩) 9 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 179 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 179) flatW_7) 9 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 179) hP hQ flatW_7 9 flatSeed_7
  have hMono : QuotientRankAtLeast step99o144ActualSource4 9 :=
    quotientRankAtLeast_mono step99o144s4_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o144s4_sourceU_le hMono

theorem step99o144_all_dispatch (i : Fin 5) :
    QuotientRankAtLeast (o144SourceU i) (o144SourceLb i) := by
  fin_cases i
  · exact step99o144s0Dispatch
  · exact step99o144s1Dispatch
  · exact step99o144s2Dispatch
  · exact step99o144s3Dispatch
  · exact step99o144s4Dispatch

theorem step99_orbit144_lb15_unconditional :
    QuotientRankAtLeast o144W 15 :=
  o144Lb15 step99o144_all_dispatch

end QiushiMatmul
