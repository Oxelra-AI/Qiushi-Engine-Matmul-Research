import QiushiCodeSpanCore
import QiushiFlattenSeeds
import QiushiMonotonicity
import QiushiOrbit14FP
import QiushiOrbitTransport
import QiushiStep98Orbit56Consumer
import QiushiTransposeTransport

set_option maxHeartbeats 800000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem step99o56_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step99o56MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step99o56_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step99o56MatrixCodeNat M) = M := by decide

lemma step99o56_codeMat_matrixCode (M : Mat3) :
    codeMat (step99o56MatrixCodeNat M) = M :=
  step99o56_codeMat_matrixCode_all M

private theorem step99o56_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step99o56_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

private theorem step99o56_codeMat_mem_transposeW_of_witness
    {V : Submodule F2 Mat3} {pre tpre : Nat}
    (h_mem : codeMat tpre ∈ V)
    (h_trans : (codeMat tpre : Mat3).transpose = codeMat pre) :
    codeMat pre ∈ transposeW V := by
  change ∃ X, X ∈ V ∧ transposeLinearMap X = codeMat pre
  exact ⟨codeMat tpre, h_mem, h_trans⟩

private theorem step99o56_eq_of_add_eq_zero {a b : F2} (h : a + b = 0) : a = b := by
  simpa only [ZMod.neg_eq_self_mod_two] using (eq_neg_iff_add_eq_zero.mpr h)

-- Source 0 (row 0): orbit 14, lb 12
def step99o56ActualSource0 : Submodule F2 Mat3 := spanCodes [256, 160, 64, 16, 12, 2, 1]

private theorem step99o56s0_sourceU_le :
    (o56SourceU ⟨0, by omega⟩) ≤ step99o56ActualSource0 := by
  intro M hM
  change evalFunc (codeMat 160) M = 0 ∧ evalFunc (codeMat 12) M = 0 at hM
  norm_num [evalFunc, codeMat, Fin.sum_univ_succ, Nat.testBit,
    Nat.shiftRight_eq_div_pow] at hM
  -- The free matrix entries give coefficients in the displayed generating family.
  have hsum : M = M 2 2 • codeMat 256 + M 2 1 • codeMat 160 +
      M 2 0 • codeMat 64 + M 1 1 • codeMat 16 + M 1 0 • codeMat 12 +
      M 0 1 • codeMat 2 + M 0 0 • codeMat 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [codeMat, Nat.testBit, Nat.shiftRight_eq_div_pow,
        Matrix.add_apply, Matrix.smul_apply] <;> try rfl
    · exact step99o56_eq_of_add_eq_zero hM.2
    · exact step99o56_eq_of_add_eq_zero hM.1
  change M ∈ spanCodes [256, 160, 64, 16, 12, 2, 1]
  rw [hsum]
  repeat' first | apply Submodule.add_mem | apply Submodule.smul_mem
  all_goals exact Submodule.subset_span ⟨_, by simp, rfl⟩

private theorem step99o56s0_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o56s0_targetSpan_le_action :
    step99o56ActualSource0 ≤ actionW (codeMat 273) (codeMat 266) orbit14W := by
  apply step99o56_spanCodes_le_of_gens [256, 160, 64, 16, 12, 2, 1]
    (actionW (codeMat 273) (codeMat 266) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 273) (codeMat 266) (codeMat 256) = codeMat 256 := by
      unfold actionA
      rw [step99o56s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 256 * (codeMat 266 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o56_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 273) (codeMat 266) (codeMat 96) = codeMat 160 := by
      unfold actionA
      rw [step99o56s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 96 * (codeMat 266 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o56_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 273) (codeMat 266) (codeMat 128) = codeMat 64 := by
      unfold actionA
      rw [step99o56s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 128 * (codeMat 266 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o56_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 266) (codeMat 8) = codeMat 16 := by
      unfold actionA
      rw [step99o56s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 266 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o56_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 20 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 20 (by decide)
    have hact : actionA (codeMat 273) (codeMat 266) (codeMat 20) = codeMat 12 := by
      unfold actionA
      rw [step99o56s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 20 * (codeMat 266 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o56_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 266) (codeMat 1) = codeMat 2 := by
      unfold actionA
      rw [step99o56s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o56_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 266) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step99o56s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o56_codeMat_mem_actionW_of_witness hw hact

theorem step99o56s0Dispatch :
    QuotientRankAtLeast (o56SourceU ⟨0, by omega⟩) 12 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 266) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 266) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step99o56ActualSource0 12 :=
    quotientRankAtLeast_mono step99o56s0_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o56s0_sourceU_le hMono

-- Source 1 (row 1): orbit 14, lb 12
def step99o56ActualSource1 : Submodule F2 Mat3 := spanCodes [256, 160, 68, 20, 12, 2, 1]

private theorem step99o56s1_sourceU_le :
    (o56SourceU ⟨1, by omega⟩) ≤ step99o56ActualSource1 := by
  intro M hM
  change evalFunc (codeMat 160) M = 0 ∧ evalFunc (codeMat 80 + codeMat 12) M = 0 at hM
  norm_num [evalFunc, codeMat, Fin.sum_univ_succ, Nat.testBit,
    Nat.shiftRight_eq_div_pow] at hM
  have hsum : M = M 2 2 • codeMat 256 + M 2 1 • codeMat 160 +
      M 2 0 • codeMat 68 + M 1 1 • codeMat 20 + M 1 0 • codeMat 12 +
      M 0 1 • codeMat 2 + M 0 0 • codeMat 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [codeMat, Nat.testBit, Nat.shiftRight_eq_div_pow,
        Matrix.add_apply, Matrix.smul_apply] <;> try rfl
    · change M 0 2 = M 2 0 + M 1 1 + M 1 0
      apply step99o56_eq_of_add_eq_zero
      calc
        M 0 2 + (M 2 0 + M 1 1 + M 1 0) =
            M 0 2 + (M 1 0 + M 1 1 + M 2 0) := by ac_rfl
        _ = 0 := hM.2
    · exact step99o56_eq_of_add_eq_zero hM.1
  change M ∈ spanCodes [256, 160, 68, 20, 12, 2, 1]
  rw [hsum]
  repeat' first | apply Submodule.add_mem | apply Submodule.smul_mem
  all_goals exact Submodule.subset_span ⟨_, by simp, rfl⟩

private theorem step99o56s1_QtInv :
    (codeMat 286 : Mat3).transpose⁻¹ = (codeMat 303 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 286 : Mat3).transpose * (codeMat 303 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o56s1_targetSpan_le_action :
    step99o56ActualSource1 ≤ actionW (codeMat 473) (codeMat 286) orbit14W := by
  apply step99o56_spanCodes_le_of_gens [256, 160, 68, 20, 12, 2, 1]
    (actionW (codeMat 473) (codeMat 286) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 473) (codeMat 286) (codeMat 360) = codeMat 256 := by
      unfold actionA
      rw [step99o56s1_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 360 * (codeMat 303 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o56_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 245 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 245 (by decide)
    have hact : actionA (codeMat 473) (codeMat 286) (codeMat 245) = codeMat 160 := by
      unfold actionA
      rw [step99o56s1_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 245 * (codeMat 303 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o56_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 149 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 149 (by decide)
    have hact : actionA (codeMat 473) (codeMat 286) (codeMat 149) = codeMat 68 := by
      unfold actionA
      rw [step99o56s1_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 149 * (codeMat 303 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o56_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 30 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 30 (by decide)
    have hact : actionA (codeMat 473) (codeMat 286) (codeMat 30) = codeMat 20 := by
      unfold actionA
      rw [step99o56s1_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 30 * (codeMat 303 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o56_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 23 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 23 (by decide)
    have hact : actionA (codeMat 473) (codeMat 286) (codeMat 23) = codeMat 12 := by
      unfold actionA
      rw [step99o56s1_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 23 * (codeMat 303 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o56_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 473) (codeMat 286) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [step99o56s1_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 3 * (codeMat 303 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o56_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 473) (codeMat 286) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step99o56s1_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 2 * (codeMat 303 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o56_codeMat_mem_actionW_of_witness hw hact

theorem step99o56s1Dispatch :
    QuotientRankAtLeast (o56SourceU ⟨1, by omega⟩) 12 := by
  have hP : Invertible (codeMat 473 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 286 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 473) (codeMat 286) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 473) (codeMat 286) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step99o56ActualSource1 12 :=
    quotientRankAtLeast_mono step99o56s1_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o56s1_sourceU_le hMono

-- Source 2 (row 2): orbit 14, lb 12
def step99o56ActualSource2 : Submodule F2 Mat3 := spanCodes [256, 128, 80, 32, 12, 2, 1]

private theorem step99o56s2_sourceU_le :
    (o56SourceU ⟨2, by omega⟩) ≤ step99o56ActualSource2 := by
  intro M hM
  change evalFunc (codeMat 80) M = 0 ∧ evalFunc (codeMat 12) M = 0 at hM
  norm_num [evalFunc, codeMat, Fin.sum_univ_succ, Nat.testBit,
    Nat.shiftRight_eq_div_pow] at hM
  have hsum : M = M 2 2 • codeMat 256 + M 2 1 • codeMat 128 +
      M 2 0 • codeMat 80 + M 1 2 • codeMat 32 + M 1 0 • codeMat 12 +
      M 0 1 • codeMat 2 + M 0 0 • codeMat 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [codeMat, Nat.testBit, Nat.shiftRight_eq_div_pow,
        Matrix.add_apply, Matrix.smul_apply] <;> try rfl
    · exact step99o56_eq_of_add_eq_zero hM.2
    · exact step99o56_eq_of_add_eq_zero hM.1
  change M ∈ spanCodes [256, 128, 80, 32, 12, 2, 1]
  rw [hsum]
  repeat' first | apply Submodule.add_mem | apply Submodule.smul_mem
  all_goals exact Submodule.subset_span ⟨_, by simp, rfl⟩

private theorem step99o56s2_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o56s2_targetSpan_le_action :
    step99o56ActualSource2 ≤ actionW (codeMat 84) (codeMat 84) orbit14W := by
  apply step99o56_spanCodes_le_of_gens [256, 128, 80, 32, 12, 2, 1]
    (actionW (codeMat 84) (codeMat 84) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step99o56s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 84 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o56_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 2) = codeMat 128 := by
      unfold actionA
      rw [step99o56s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 84 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o56_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 20 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 20 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 20) = codeMat 80 := by
      unfold actionA
      rw [step99o56s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 20 * (codeMat 84 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o56_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step99o56s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 84 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o56_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 96) = codeMat 12 := by
      unfold actionA
      rw [step99o56s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 96 * (codeMat 84 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o56_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 128) = codeMat 2 := by
      unfold actionA
      rw [step99o56s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 84 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o56_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step99o56s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 84 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o56_codeMat_mem_actionW_of_witness hw hact

theorem step99o56s2Dispatch :
    QuotientRankAtLeast (o56SourceU ⟨2, by omega⟩) 12 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 84) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 84) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step99o56ActualSource2 12 :=
    quotientRankAtLeast_mono step99o56s2_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o56s2_sourceU_le hMono

-- Source 3 (row 3): orbit 14, lb 12
def step99o56ActualSource3 : Submodule F2 Mat3 := spanCodes [256, 132, 80, 36, 12, 2, 1]

private theorem step99o56s3_sourceU_le :
    (o56SourceU ⟨3, by omega⟩) ≤ step99o56ActualSource3 := by
  intro M hM
  change evalFunc (codeMat 160 + codeMat 12) M = 0 ∧ evalFunc (codeMat 80) M = 0 at hM
  norm_num [evalFunc, codeMat, Fin.sum_univ_succ, Nat.testBit,
    Nat.shiftRight_eq_div_pow] at hM
  have hsum : M = M 2 2 • codeMat 256 + M 2 1 • codeMat 132 +
      M 2 0 • codeMat 80 + M 1 2 • codeMat 36 + M 1 0 • codeMat 12 +
      M 0 1 • codeMat 2 + M 0 0 • codeMat 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [codeMat, Nat.testBit, Nat.shiftRight_eq_div_pow,
        Matrix.add_apply, Matrix.smul_apply] <;> try rfl
    · change M 0 2 = M 2 1 + M 1 2 + M 1 0
      apply step99o56_eq_of_add_eq_zero
      calc
        M 0 2 + (M 2 1 + M 1 2 + M 1 0) =
            M 0 2 + (M 1 0 + M 1 2 + M 2 1) := by ac_rfl
        _ = 0 := hM.1
    · exact step99o56_eq_of_add_eq_zero hM.2
  change M ∈ spanCodes [256, 132, 80, 36, 12, 2, 1]
  rw [hsum]
  repeat' first | apply Submodule.add_mem | apply Submodule.smul_mem
  all_goals exact Submodule.subset_span ⟨_, by simp, rfl⟩

private theorem step99o56s3_QtInv :
    (codeMat 204 : Mat3).transpose⁻¹ = (codeMat 114 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 204 : Mat3).transpose * (codeMat 114 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o56s3_targetSpan_le_action :
    step99o56ActualSource3 ≤ actionW (codeMat 103) (codeMat 204) orbit14W := by
  apply step99o56_spanCodes_le_of_gens [256, 132, 80, 36, 12, 2, 1]
    (actionW (codeMat 103) (codeMat 204) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 103) (codeMat 204) (codeMat 8) = codeMat 256 := by
      unfold actionA
      rw [step99o56s3_QtInv]
      show (codeMat 103 : Mat3).transpose * codeMat 8 * (codeMat 114 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o56_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 103) (codeMat 204) (codeMat 96) = codeMat 132 := by
      unfold actionA
      rw [step99o56s3_QtInv]
      show (codeMat 103 : Mat3).transpose * codeMat 96 * (codeMat 114 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o56_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 276 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 276 (by decide)
    have hact : actionA (codeMat 103) (codeMat 204) (codeMat 276) = codeMat 80 := by
      unfold actionA
      rw [step99o56s3_QtInv]
      show (codeMat 103 : Mat3).transpose * codeMat 276 * (codeMat 114 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o56_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 9 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 9 (by decide)
    have hact : actionA (codeMat 103) (codeMat 204) (codeMat 9) = codeMat 36 := by
      unfold actionA
      rw [step99o56s3_QtInv]
      show (codeMat 103 : Mat3).transpose * codeMat 9 * (codeMat 114 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o56_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 502 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 502 (by decide)
    have hact : actionA (codeMat 103) (codeMat 204) (codeMat 502) = codeMat 12 := by
      unfold actionA
      rw [step99o56s3_QtInv]
      show (codeMat 103 : Mat3).transpose * codeMat 502 * (codeMat 114 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o56_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 103) (codeMat 204) (codeMat 256) = codeMat 2 := by
      unfold actionA
      rw [step99o56s3_QtInv]
      show (codeMat 103 : Mat3).transpose * codeMat 256 * (codeMat 114 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o56_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 103) (codeMat 204) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step99o56s3_QtInv]
      show (codeMat 103 : Mat3).transpose * codeMat 384 * (codeMat 114 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o56_codeMat_mem_actionW_of_witness hw hact

theorem step99o56s3Dispatch :
    QuotientRankAtLeast (o56SourceU ⟨3, by omega⟩) 12 := by
  have hP : Invertible (codeMat 103 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 204 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 103) (codeMat 204) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 103) (codeMat 204) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step99o56ActualSource3 12 :=
    quotientRankAtLeast_mono step99o56s3_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o56s3_sourceU_le hMono

-- Source 4 (row 13): orbit 2, lb 6
def step99o56ActualSource4 : Submodule F2 Mat3 := spanCodes [256, 144, 80, 48, 8, 4, 2, 1]

private theorem step99o56s4_sourceU_le :
    (o56SourceU ⟨4, by omega⟩) ≤ step99o56ActualSource4 := by
  intro M hM
  change evalFunc (codeMat 160 + codeMat 80) M = 0 at hM
  norm_num [evalFunc, codeMat, Fin.sum_univ_succ, Nat.testBit,
    Nat.shiftRight_eq_div_pow] at hM
  have hsum : M = M 2 2 • codeMat 256 + M 2 1 • codeMat 144 +
      M 2 0 • codeMat 80 + M 1 2 • codeMat 48 + M 1 0 • codeMat 8 +
      M 0 2 • codeMat 4 + M 0 1 • codeMat 2 + M 0 0 • codeMat 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [codeMat, Nat.testBit, Nat.shiftRight_eq_div_pow,
        Matrix.add_apply, Matrix.smul_apply] <;> try rfl
    change M 1 1 = M 2 1 + M 2 0 + M 1 2
    apply step99o56_eq_of_add_eq_zero
    calc
      M 1 1 + (M 2 1 + M 2 0 + M 1 2) =
          M 1 1 + M 1 2 + (M 2 0 + M 2 1) := by ac_rfl
      _ = 0 := hM
  change M ∈ spanCodes [256, 144, 80, 48, 8, 4, 2, 1]
  rw [hsum]
  repeat' first | apply Submodule.add_mem | apply Submodule.smul_mem
  all_goals exact Submodule.subset_span ⟨_, by simp, rfl⟩

private theorem step99o56s4_QtInv :
    (codeMat 244 : Mat3).transpose⁻¹ = (codeMat 95 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 244 : Mat3).transpose * (codeMat 95 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o56s4_targetSpan_le_action :
    step99o56ActualSource4 ≤ actionW (codeMat 161) (codeMat 244) flatW_2 := by
  apply step99o56_spanCodes_le_of_gens [256, 144, 80, 48, 8, 4, 2, 1]
    (actionW (codeMat 161) (codeMat 244) flatW_2)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 24 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 24 (by decide)
    have hact : actionA (codeMat 161) (codeMat 244) (codeMat 24) = codeMat 256 := by
      unfold actionA
      rw [step99o56s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 24 * (codeMat 95 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o56_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 432 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 432 (by decide)
    have hact : actionA (codeMat 161) (codeMat 244) (codeMat 432) = codeMat 144 := by
      unfold actionA
      rw [step99o56s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 432 * (codeMat 95 : Mat3).transpose = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o56_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 416 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 416 (by decide)
    have hact : actionA (codeMat 161) (codeMat 244) (codeMat 416) = codeMat 80 := by
      unfold actionA
      rw [step99o56s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 416 * (codeMat 95 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o56_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 320 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 320 (by decide)
    have hact : actionA (codeMat 161) (codeMat 244) (codeMat 320) = codeMat 48 := by
      unfold actionA
      rw [step99o56s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 320 * (codeMat 95 : Mat3).transpose = codeMat 48
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o56_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 256 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 161) (codeMat 244) (codeMat 256) = codeMat 8 := by
      unfold actionA
      rw [step99o56s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 256 * (codeMat 95 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o56_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 3 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 161) (codeMat 244) (codeMat 3) = codeMat 4 := by
      unfold actionA
      rw [step99o56s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 3 * (codeMat 95 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o56_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 6 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 6 (by decide)
    have hact : actionA (codeMat 161) (codeMat 244) (codeMat 6) = codeMat 2 := by
      unfold actionA
      rw [step99o56s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 6 * (codeMat 95 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o56_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 4 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 4 (by decide)
    have hact : actionA (codeMat 161) (codeMat 244) (codeMat 4) = codeMat 1 := by
      unfold actionA
      rw [step99o56s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 4 * (codeMat 95 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o56_codeMat_mem_actionW_of_witness hw hact

theorem step99o56s4Dispatch :
    QuotientRankAtLeast (o56SourceU ⟨4, by omega⟩) 6 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 244 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 244) flatW_2) 6 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 244) hP hQ flatW_2 6 flatSeed_2
  have hMono : QuotientRankAtLeast step99o56ActualSource4 6 :=
    quotientRankAtLeast_mono step99o56s4_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o56s4_sourceU_le hMono

theorem step99o56_all_dispatch (i : Fin 5) :
    QuotientRankAtLeast (o56SourceU i) (o56SourceLb i) := by
  fin_cases i
  · exact step99o56s0Dispatch
  · exact step99o56s1Dispatch
  · exact step99o56s2Dispatch
  · exact step99o56s3Dispatch
  · exact step99o56s4Dispatch

theorem step99_orbit56_lb14_unconditional :
    QuotientRankAtLeast o56W 14 :=
  o56Lb14 step99o56_all_dispatch

end QiushiMatmul
