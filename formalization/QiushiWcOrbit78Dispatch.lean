import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit78Consumer
import QiushiOrbit14FP
import QiushiFlattenSeeds

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc78_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc78_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc78s0_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc78s0_contain :
    (o78SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 337) (codeMat 273) orbit14W := by
  change spanCodes [260, 128, 96, 20, 8, 2, 1] ≤ actionW (codeMat 337) (codeMat 273) orbit14W
  apply step109wc78_spanCodes_le_of_gens [260, 128, 96, 20, 8, 2, 1]
    (actionW (codeMat 337) (codeMat 273) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 337) (codeMat 273) (codeMat 256) = codeMat 260 := by
      unfold actionA
      rw [step109wc78s0_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 256 * (codeMat 273 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc78_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 130 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 130 (by decide)
    have hact : actionA (codeMat 337) (codeMat 273) (codeMat 130) = codeMat 128 := by
      unfold actionA
      rw [step109wc78s0_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 130 * (codeMat 273 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc78_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 97 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 97 (by decide)
    have hact : actionA (codeMat 337) (codeMat 273) (codeMat 97) = codeMat 96 := by
      unfold actionA
      rw [step109wc78s0_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 97 * (codeMat 273 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc78_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 20 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 20 (by decide)
    have hact : actionA (codeMat 337) (codeMat 273) (codeMat 20) = codeMat 20 := by
      unfold actionA
      rw [step109wc78s0_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 20 * (codeMat 273 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc78_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 337) (codeMat 273) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step109wc78s0_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 8 * (codeMat 273 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc78_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 337) (codeMat 273) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc78s0_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc78_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 337) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc78s0_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc78_codeMat_mem_actionW_of_witness hw hact

theorem step109wc78s0Dispatch :
    QuotientRankAtLeast (o78SourceU_wc ⟨0, by omega⟩) 12 := by
  have hP : Invertible (codeMat 337 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 337) (codeMat 273) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 337) (codeMat 273) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc78s0_contain hAct


private theorem step109wc78s1_QtInv :
    (codeMat 354 : Mat3).transpose⁻¹ = (codeMat 142 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 354 : Mat3).transpose * (codeMat 142 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc78s1_contain :
    (o78SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 86) (codeMat 354) orbit14W := by
  change spanCodes [258, 128, 96, 16, 10, 4, 1] ≤ actionW (codeMat 86) (codeMat 354) orbit14W
  apply step109wc78_spanCodes_le_of_gens [258, 128, 96, 16, 10, 4, 1]
    (actionW (codeMat 86) (codeMat 354) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 118 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 118 (by decide)
    have hact : actionA (codeMat 86) (codeMat 354) (codeMat 118) = codeMat 258 := by
      unfold actionA
      rw [step109wc78s1_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 118 * (codeMat 142 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc78_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 9 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 9 (by decide)
    have hact : actionA (codeMat 86) (codeMat 354) (codeMat 9) = codeMat 128 := by
      unfold actionA
      rw [step109wc78s1_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 9 * (codeMat 142 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc78_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 20 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 20 (by decide)
    have hact : actionA (codeMat 86) (codeMat 354) (codeMat 20) = codeMat 96 := by
      unfold actionA
      rw [step109wc78s1_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 20 * (codeMat 142 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc78_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 86) (codeMat 354) (codeMat 8) = codeMat 16 := by
      unfold actionA
      rw [step109wc78s1_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 8 * (codeMat 142 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc78_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 86) (codeMat 354) (codeMat 96) = codeMat 10 := by
      unfold actionA
      rw [step109wc78s1_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 96 * (codeMat 142 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc78_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 86) (codeMat 354) (codeMat 384) = codeMat 4 := by
      unfold actionA
      rw [step109wc78s1_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 384 * (codeMat 142 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc78_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 86) (codeMat 354) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc78s1_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 256 * (codeMat 142 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc78_codeMat_mem_actionW_of_witness hw hact

theorem step109wc78s1Dispatch :
    QuotientRankAtLeast (o78SourceU_wc ⟨1, by omega⟩) 12 := by
  have hP : Invertible (codeMat 86 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 354 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 86) (codeMat 354) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 86) (codeMat 354) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc78s1_contain hAct


private theorem step109wc78s2_QtInv :
    (codeMat 428 : Mat3).transpose⁻¹ = (codeMat 107 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 428 : Mat3).transpose * (codeMat 107 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc78s2_contain :
    (o78SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 285) (codeMat 428) orbit14W := by
  change spanCodes [262, 128, 64, 32, 20, 10, 1] ≤ actionW (codeMat 285) (codeMat 428) orbit14W
  apply step109wc78_spanCodes_le_of_gens [262, 128, 64, 32, 20, 10, 1]
    (actionW (codeMat 285) (codeMat 428) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 259 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 259 (by decide)
    have hact : actionA (codeMat 285) (codeMat 428) (codeMat 259) = codeMat 262 := by
      unfold actionA
      rw [step109wc78s2_QtInv]
      show (codeMat 285 : Mat3).transpose * codeMat 259 * (codeMat 107 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc78_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 285) (codeMat 428) (codeMat 256) = codeMat 128 := by
      unfold actionA
      rw [step109wc78s2_QtInv]
      show (codeMat 285 : Mat3).transpose * codeMat 256 * (codeMat 107 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc78_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 285) (codeMat 428) (codeMat 128) = codeMat 64 := by
      unfold actionA
      rw [step109wc78s2_QtInv]
      show (codeMat 285 : Mat3).transpose * codeMat 128 * (codeMat 107 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc78_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 511 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 511 (by decide)
    have hact : actionA (codeMat 285) (codeMat 428) (codeMat 511) = codeMat 32 := by
      unfold actionA
      rw [step109wc78s2_QtInv]
      show (codeMat 285 : Mat3).transpose * codeMat 511 * (codeMat 107 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc78_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 227 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 227 (by decide)
    have hact : actionA (codeMat 285) (codeMat 428) (codeMat 227) = codeMat 20 := by
      unfold actionA
      rw [step109wc78s2_QtInv]
      show (codeMat 285 : Mat3).transpose * codeMat 227 * (codeMat 107 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc78_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 406 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 406 (by decide)
    have hact : actionA (codeMat 285) (codeMat 428) (codeMat 406) = codeMat 10 := by
      unfold actionA
      rw [step109wc78s2_QtInv]
      show (codeMat 285 : Mat3).transpose * codeMat 406 * (codeMat 107 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc78_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 130 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 130 (by decide)
    have hact : actionA (codeMat 285) (codeMat 428) (codeMat 130) = codeMat 1 := by
      unfold actionA
      rw [step109wc78s2_QtInv]
      show (codeMat 285 : Mat3).transpose * codeMat 130 * (codeMat 107 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc78_codeMat_mem_actionW_of_witness hw hact

theorem step109wc78s2Dispatch :
    QuotientRankAtLeast (o78SourceU_wc ⟨2, by omega⟩) 12 := by
  have hP : Invertible (codeMat 285 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 428 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 285) (codeMat 428) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 285) (codeMat 428) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc78s2_contain hAct


private theorem step109wc78s3_QtInv :
    (codeMat 379 : Mat3).transpose⁻¹ = (codeMat 247 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 379 : Mat3).transpose * (codeMat 247 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc78s3_contain :
    (o78SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 412) (codeMat 379) orbit14W := by
  change spanCodes [262, 128, 70, 38, 20, 10, 1] ≤ actionW (codeMat 412) (codeMat 379) orbit14W
  apply step109wc78_spanCodes_le_of_gens [262, 128, 70, 38, 20, 10, 1]
    (actionW (codeMat 412) (codeMat 379) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 363 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 363 (by decide)
    have hact : actionA (codeMat 412) (codeMat 379) (codeMat 363) = codeMat 262 := by
      unfold actionA
      rw [step109wc78s3_QtInv]
      show (codeMat 412 : Mat3).transpose * codeMat 363 * (codeMat 247 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc78_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 412) (codeMat 379) (codeMat 3) = codeMat 128 := by
      unfold actionA
      rw [step109wc78s3_QtInv]
      show (codeMat 412 : Mat3).transpose * codeMat 3 * (codeMat 247 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc78_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 362 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 362 (by decide)
    have hact : actionA (codeMat 412) (codeMat 379) (codeMat 362) = codeMat 70 := by
      unfold actionA
      rw [step109wc78s3_QtInv]
      show (codeMat 412 : Mat3).transpose * codeMat 362 * (codeMat 247 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc78_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 235 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 235 (by decide)
    have hact : actionA (codeMat 412) (codeMat 379) (codeMat 235) = codeMat 38 := by
      unfold actionA
      rw [step109wc78s3_QtInv]
      show (codeMat 412 : Mat3).transpose * codeMat 235 * (codeMat 247 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc78_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 373 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 373 (by decide)
    have hact : actionA (codeMat 412) (codeMat 379) (codeMat 373) = codeMat 20 := by
      unfold actionA
      rw [step109wc78s3_QtInv]
      show (codeMat 412 : Mat3).transpose * codeMat 373 * (codeMat 247 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc78_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 284 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 284 (by decide)
    have hact : actionA (codeMat 412) (codeMat 379) (codeMat 284) = codeMat 10 := by
      unfold actionA
      rw [step109wc78s3_QtInv]
      show (codeMat 412 : Mat3).transpose * codeMat 284 * (codeMat 247 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc78_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 511 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 511 (by decide)
    have hact : actionA (codeMat 412) (codeMat 379) (codeMat 511) = codeMat 1 := by
      unfold actionA
      rw [step109wc78s3_QtInv]
      show (codeMat 412 : Mat3).transpose * codeMat 511 * (codeMat 247 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc78_codeMat_mem_actionW_of_witness hw hact

theorem step109wc78s3Dispatch :
    QuotientRankAtLeast (o78SourceU_wc ⟨3, by omega⟩) 12 := by
  have hP : Invertible (codeMat 412 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 379 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 412) (codeMat 379) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 412) (codeMat 379) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc78s3_contain hAct


private theorem step109wc78s4_QtInv :
    (codeMat 498 : Mat3).transpose⁻¹ = (codeMat 206 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 498 : Mat3).transpose * (codeMat 206 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc78s4_contain :
    (o78SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 87) (codeMat 498) flatW_2 := by
  change spanCodes [256, 128, 66, 34, 18, 10, 6, 1] ≤ actionW (codeMat 87) (codeMat 498) flatW_2
  apply step109wc78_spanCodes_le_of_gens [256, 128, 66, 34, 18, 10, 6, 1]
    (actionW (codeMat 87) (codeMat 498) flatW_2)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 438 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 438 (by decide)
    have hact : actionA (codeMat 87) (codeMat 498) (codeMat 438) = codeMat 256 := by
      unfold actionA
      rw [step109wc78s4_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 438 * (codeMat 206 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc78_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 511 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 511 (by decide)
    have hact : actionA (codeMat 87) (codeMat 498) (codeMat 511) = codeMat 128 := by
      unfold actionA
      rw [step109wc78s4_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 511 * (codeMat 206 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc78_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 228 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 228 (by decide)
    have hact : actionA (codeMat 87) (codeMat 498) (codeMat 228) = codeMat 66 := by
      unfold actionA
      rw [step109wc78s4_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 228 * (codeMat 206 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc78_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 496 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 496 (by decide)
    have hact : actionA (codeMat 87) (codeMat 498) (codeMat 496) = codeMat 34 := by
      unfold actionA
      rw [step109wc78s4_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 496 * (codeMat 206 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc78_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 504 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 504 (by decide)
    have hact : actionA (codeMat 87) (codeMat 498) (codeMat 504) = codeMat 18 := by
      unfold actionA
      rw [step109wc78s4_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 504 * (codeMat 206 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc78_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 480 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 480 (by decide)
    have hact : actionA (codeMat 87) (codeMat 498) (codeMat 480) = codeMat 10 := by
      unfold actionA
      rw [step109wc78s4_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 480 * (codeMat 206 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc78_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 64 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 64 (by decide)
    have hact : actionA (codeMat 87) (codeMat 498) (codeMat 64) = codeMat 6 := by
      unfold actionA
      rw [step109wc78s4_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 64 * (codeMat 206 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc78_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 256 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 87) (codeMat 498) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc78s4_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 256 * (codeMat 206 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc78_codeMat_mem_actionW_of_witness hw hact

theorem step109wc78s4Dispatch :
    QuotientRankAtLeast (o78SourceU_wc ⟨4, by omega⟩) 6 := by
  have hP : Invertible (codeMat 87 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 498 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 87) (codeMat 498) flatW_2) 6 :=
    @quotientRankAtLeast_action (codeMat 87) (codeMat 498) hP hQ flatW_2 6
      flatSeed_2
  exact quotientRankAtLeast_mono step109wc78s4_contain hAct

theorem step109wc78_all_dispatch (i : Fin 5) :
    QuotientRankAtLeast (o78SourceU_wc i) (o78SourceLb_wc i) := by
  fin_cases i
  · exact step109wc78s0Dispatch
  · exact step109wc78s1Dispatch
  · exact step109wc78s2Dispatch
  · exact step109wc78s3Dispatch
  · exact step109wc78s4Dispatch

theorem step109_orbit78_lb14_wc : QuotientRankAtLeast o78W_wc 14 :=
  o78Lb14_wc step109wc78_all_dispatch

end QiushiMatmul
