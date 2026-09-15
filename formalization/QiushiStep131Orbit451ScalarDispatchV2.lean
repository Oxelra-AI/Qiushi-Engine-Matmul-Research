import QiushiStep131Orbit451CoreBoolV3
import QiushiStep128Orbit451Bridges
import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiFlattenSeeds
import QiushiOrbit10FP
import QiushiOrbit31FP
import QiushiStep107Orbit373Extraction
import QiushiStep81Qdim2Generated
import QiushiStep99Orbit196Dispatch
import QiushiStep99Orbit65Dispatch

set_option maxHeartbeats 800000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
open BigOperators Finset Matrix Classical
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem o451_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by intro M hM; rcases hM with ⟨n, hn, rfl⟩; exact h n hn)

private theorem o451_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  exact ⟨codeMat witness, h_mem, h_action⟩


  /-- Current `quotientRankAtLeast_action` has implicit `P,Q` and needs
  explicit invertibility instances.  Generated dispatch sources use matrix
  codes, so we expose a code-level wrapper whose determinant obligations remain
  closed finite checks. -/
  private theorem o451_qra_action_code (Pcode Qcode : Nat)
      {W : Submodule F2 Mat3} {n : ℕ}
      (hPdet : IsUnit (codeMat Pcode : Mat3).det)
      (hQdet : IsUnit (codeMat Qcode : Mat3).det)
      (h : QuotientRankAtLeast W n) :
      QuotientRankAtLeast (actionW (codeMat Pcode) (codeMat Qcode) W) n := by
    have hP : Invertible (codeMat Pcode : Mat3) := Matrix.invertibleOfIsUnitDet _ hPdet
    have hQ : Invertible (codeMat Qcode : Mat3) := Matrix.invertibleOfIsUnitDet _ hQdet
    exact @quotientRankAtLeast_action (codeMat Pcode) (codeMat Qcode) hP hQ W n h

-- Source 0: orbit 373, lb=17, action, P=214, Q=397, Qinv=250
private theorem o451d_s0_QtInv :
    (codeMat 397 : Mat3).transpose⁻¹ = (codeMat 250 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 397 : Mat3).transpose * (codeMat 250 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s0_actual_le_transport :
    o451ActualSourceSpan ⟨0, by omega⟩ ≤ actionW (codeMat 214) (codeMat 397) o373W := by
  apply o451_spanCodes_le_of_gens [257, 162, 19, 10]
    (actionW (codeMat 214) (codeMat 397) o373W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 245 (by decide))
      (by unfold actionA; rw [o451d_s0_QtInv]; show (codeMat 214 : Mat3).transpose * codeMat 245 * (codeMat 250 : Mat3).transpose = codeMat 257; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 300 (by decide))
      (by unfold actionA; rw [o451d_s0_QtInv]; show (codeMat 214 : Mat3).transpose * codeMat 300 * (codeMat 250 : Mat3).transpose = codeMat 162; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 472 (by decide))
      (by unfold actionA; rw [o451d_s0_QtInv]; show (codeMat 214 : Mat3).transpose * codeMat 472 * (codeMat 250 : Mat3).transpose = codeMat 19; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 312 (by decide))
      (by unfold actionA; rw [o451d_s0_QtInv]; show (codeMat 214 : Mat3).transpose * codeMat 312 * (codeMat 250 : Mat3).transpose = codeMat 10; ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o451d_s0_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨0, by omega⟩) 17 :=
  quotientRankAtLeast_mono o451d_s0_actual_le_transport (o451_qra_action_code 214 397 (by decide) (by decide) step107_orbit373_lb17)

private theorem o451d_s0_qra : QuotientRankAtLeast (o451SourceU ⟨0, by omega⟩) 17 :=
  quotientRankAtLeast_mono o451s0_sourceU_le_actual o451d_s0_qra_actual

-- Source 1: orbit 373, lb=17, action, P=141, Q=351, Qinv=239
private theorem o451d_s1_QtInv :
    (codeMat 351 : Mat3).transpose⁻¹ = (codeMat 239 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 351 : Mat3).transpose * (codeMat 239 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s1_actual_le_transport :
    o451ActualSourceSpan ⟨1, by omega⟩ ≤ actionW (codeMat 141) (codeMat 351) o373W := by
  apply o451_spanCodes_le_of_gens [257, 198, 19, 10]
    (actionW (codeMat 141) (codeMat 351) o373W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 21 (by decide))
      (by unfold actionA; rw [o451d_s1_QtInv]; show (codeMat 141 : Mat3).transpose * codeMat 21 * (codeMat 239 : Mat3).transpose = codeMat 257; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 20 (by decide))
      (by unfold actionA; rw [o451d_s1_QtInv]; show (codeMat 141 : Mat3).transpose * codeMat 20 * (codeMat 239 : Mat3).transpose = codeMat 198; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 224 (by decide))
      (by unfold actionA; rw [o451d_s1_QtInv]; show (codeMat 141 : Mat3).transpose * codeMat 224 * (codeMat 239 : Mat3).transpose = codeMat 19; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 472 (by decide))
      (by unfold actionA; rw [o451d_s1_QtInv]; show (codeMat 141 : Mat3).transpose * codeMat 472 * (codeMat 239 : Mat3).transpose = codeMat 10; ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o451d_s1_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨1, by omega⟩) 17 :=
  quotientRankAtLeast_mono o451d_s1_actual_le_transport (o451_qra_action_code 141 351 (by decide) (by decide) step107_orbit373_lb17)

private theorem o451d_s1_qra : QuotientRankAtLeast (o451SourceU ⟨1, by omega⟩) 17 :=
  quotientRankAtLeast_mono o451s1_sourceU_le_actual o451d_s1_qra_actual

-- Source 2: orbit 373, lb=17, action, P=205, Q=461, Qinv=234
private theorem o451d_s2_QtInv :
    (codeMat 461 : Mat3).transpose⁻¹ = (codeMat 234 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 461 : Mat3).transpose * (codeMat 234 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s2_actual_le_transport :
    o451ActualSourceSpan ⟨2, by omega⟩ ≤ actionW (codeMat 205) (codeMat 461) o373W := by
  apply o451_spanCodes_le_of_gens [257, 135, 19, 10]
    (actionW (codeMat 205) (codeMat 461) o373W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 21 (by decide))
      (by unfold actionA; rw [o451d_s2_QtInv]; show (codeMat 205 : Mat3).transpose * codeMat 21 * (codeMat 234 : Mat3).transpose = codeMat 257; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 20 (by decide))
      (by unfold actionA; rw [o451d_s2_QtInv]; show (codeMat 205 : Mat3).transpose * codeMat 20 * (codeMat 234 : Mat3).transpose = codeMat 135; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 312 (by decide))
      (by unfold actionA; rw [o451d_s2_QtInv]; show (codeMat 205 : Mat3).transpose * codeMat 312 * (codeMat 234 : Mat3).transpose = codeMat 19; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 472 (by decide))
      (by unfold actionA; rw [o451d_s2_QtInv]; show (codeMat 205 : Mat3).transpose * codeMat 472 * (codeMat 234 : Mat3).transpose = codeMat 10; ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o451d_s2_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨2, by omega⟩) 17 :=
  quotientRankAtLeast_mono o451d_s2_actual_le_transport (o451_qra_action_code 205 461 (by decide) (by decide) step107_orbit373_lb17)

private theorem o451d_s2_qra : QuotientRankAtLeast (o451SourceU ⟨2, by omega⟩) 17 :=
  quotientRankAtLeast_mono o451s2_sourceU_le_actual o451d_s2_qra_actual

-- Source 3: orbit 373, lb=17, action, P=159, Q=415, Qinv=253
private theorem o451d_s3_QtInv :
    (codeMat 415 : Mat3).transpose⁻¹ = (codeMat 253 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 415 : Mat3).transpose * (codeMat 253 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s3_actual_le_transport :
    o451ActualSourceSpan ⟨3, by omega⟩ ≤ actionW (codeMat 159) (codeMat 415) o373W := by
  apply o451_spanCodes_le_of_gens [257, 231, 19, 10]
    (actionW (codeMat 159) (codeMat 415) o373W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 245 (by decide))
      (by unfold actionA; rw [o451d_s3_QtInv]; show (codeMat 159 : Mat3).transpose * codeMat 245 * (codeMat 253 : Mat3).transpose = codeMat 257; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 300 (by decide))
      (by unfold actionA; rw [o451d_s3_QtInv]; show (codeMat 159 : Mat3).transpose * codeMat 300 * (codeMat 253 : Mat3).transpose = codeMat 231; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 224 (by decide))
      (by unfold actionA; rw [o451d_s3_QtInv]; show (codeMat 159 : Mat3).transpose * codeMat 224 * (codeMat 253 : Mat3).transpose = codeMat 19; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 312 (by decide))
      (by unfold actionA; rw [o451d_s3_QtInv]; show (codeMat 159 : Mat3).transpose * codeMat 312 * (codeMat 253 : Mat3).transpose = codeMat 10; ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o451d_s3_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨3, by omega⟩) 17 :=
  quotientRankAtLeast_mono o451d_s3_actual_le_transport (o451_qra_action_code 159 415 (by decide) (by decide) step107_orbit373_lb17)

private theorem o451d_s3_qra : QuotientRankAtLeast (o451SourceU ⟨3, by omega⟩) 17 :=
  quotientRankAtLeast_mono o451s3_sourceU_le_actual o451d_s3_qra_actual

-- Source 4: orbit 373, lb=17, action, P=95, Q=470, Qinv=213
private theorem o451d_s4_QtInv :
    (codeMat 470 : Mat3).transpose⁻¹ = (codeMat 213 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 470 : Mat3).transpose * (codeMat 213 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s4_actual_le_transport :
    o451ActualSourceSpan ⟨4, by omega⟩ ≤ actionW (codeMat 95) (codeMat 470) o373W := by
  apply o451_spanCodes_le_of_gens [257, 102, 19, 10]
    (actionW (codeMat 95) (codeMat 470) o373W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 301 (by decide))
      (by unfold actionA; rw [o451d_s4_QtInv]; show (codeMat 95 : Mat3).transpose * codeMat 301 * (codeMat 213 : Mat3).transpose = codeMat 257; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 460 (by decide))
      (by unfold actionA; rw [o451d_s4_QtInv]; show (codeMat 95 : Mat3).transpose * codeMat 460 * (codeMat 213 : Mat3).transpose = codeMat 102; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 312 (by decide))
      (by unfold actionA; rw [o451d_s4_QtInv]; show (codeMat 95 : Mat3).transpose * codeMat 312 * (codeMat 213 : Mat3).transpose = codeMat 19; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 224 (by decide))
      (by unfold actionA; rw [o451d_s4_QtInv]; show (codeMat 95 : Mat3).transpose * codeMat 224 * (codeMat 213 : Mat3).transpose = codeMat 10; ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o451d_s4_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨4, by omega⟩) 17 :=
  quotientRankAtLeast_mono o451d_s4_actual_le_transport (o451_qra_action_code 95 470 (by decide) (by decide) step107_orbit373_lb17)

private theorem o451d_s4_qra : QuotientRankAtLeast (o451SourceU ⟨4, by omega⟩) 17 :=
  quotientRankAtLeast_mono o451s4_sourceU_le_actual o451d_s4_qra_actual

-- Source 5: orbit 373, lb=17, action, P=86, Q=342, Qinv=215
private theorem o451d_s5_QtInv :
    (codeMat 342 : Mat3).transpose⁻¹ = (codeMat 215 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 342 : Mat3).transpose * (codeMat 215 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s5_actual_le_transport :
    o451ActualSourceSpan ⟨5, by omega⟩ ≤ actionW (codeMat 86) (codeMat 342) o373W := by
  apply o451_spanCodes_le_of_gens [257, 99, 19, 10]
    (actionW (codeMat 86) (codeMat 342) o373W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 301 (by decide))
      (by unfold actionA; rw [o451d_s5_QtInv]; show (codeMat 86 : Mat3).transpose * codeMat 301 * (codeMat 215 : Mat3).transpose = codeMat 257; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 460 (by decide))
      (by unfold actionA; rw [o451d_s5_QtInv]; show (codeMat 86 : Mat3).transpose * codeMat 460 * (codeMat 215 : Mat3).transpose = codeMat 99; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 472 (by decide))
      (by unfold actionA; rw [o451d_s5_QtInv]; show (codeMat 86 : Mat3).transpose * codeMat 472 * (codeMat 215 : Mat3).transpose = codeMat 19; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 224 (by decide))
      (by unfold actionA; rw [o451d_s5_QtInv]; show (codeMat 86 : Mat3).transpose * codeMat 224 * (codeMat 215 : Mat3).transpose = codeMat 10; ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o451d_s5_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨5, by omega⟩) 17 :=
  quotientRankAtLeast_mono o451d_s5_actual_le_transport (o451_qra_action_code 86 342 (by decide) (by decide) step107_orbit373_lb17)

private theorem o451d_s5_qra : QuotientRankAtLeast (o451SourceU ⟨5, by omega⟩) 17 :=
  quotientRankAtLeast_mono o451s5_sourceU_le_actual o451d_s5_qra_actual

-- Source 6: orbit 196, lb=16, action, P=244, Q=348, Qinv=125
private theorem o451d_s6_QtInv :
    (codeMat 348 : Mat3).transpose⁻¹ = (codeMat 125 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 348 : Mat3).transpose * (codeMat 125 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s6_actual_le_transport :
    o451ActualSourceSpan ⟨6, by omega⟩ ≤ actionW (codeMat 244) (codeMat 348) o196W := by
  apply o451_spanCodes_le_of_gens [257, 161, 96, 19, 10]
    (actionW (codeMat 244) (codeMat 348) o196W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 435 (by decide))
      (by unfold actionA; rw [o451d_s6_QtInv]; show (codeMat 244 : Mat3).transpose * codeMat 435 * (codeMat 125 : Mat3).transpose = codeMat 257; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 409 (by decide))
      (by unfold actionA; rw [o451d_s6_QtInv]; show (codeMat 244 : Mat3).transpose * codeMat 409 * (codeMat 125 : Mat3).transpose = codeMat 161; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 43 (by decide))
      (by unfold actionA; rw [o451d_s6_QtInv]; show (codeMat 244 : Mat3).transpose * codeMat 43 * (codeMat 125 : Mat3).transpose = codeMat 96; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 310 (by decide))
      (by unfold actionA; rw [o451d_s6_QtInv]; show (codeMat 244 : Mat3).transpose * codeMat 310 * (codeMat 125 : Mat3).transpose = codeMat 19; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 164 (by decide))
      (by unfold actionA; rw [o451d_s6_QtInv]; show (codeMat 244 : Mat3).transpose * codeMat 164 * (codeMat 125 : Mat3).transpose = codeMat 10; ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o451d_s6_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨6, by omega⟩) 16 :=
  quotientRankAtLeast_mono o451d_s6_actual_le_transport (o451_qra_action_code 244 348 (by decide) (by decide) step99_orbit196_lb16_unconditional)

private theorem o451d_s6_qra : QuotientRankAtLeast (o451SourceU ⟨6, by omega⟩) 16 :=
  quotientRankAtLeast_mono o451s6_sourceU_le_actual o451d_s6_qra_actual

-- Source 7: orbit 196, lb=16, action, P=188, Q=460, Qinv=122
private theorem o451d_s7_QtInv :
    (codeMat 460 : Mat3).transpose⁻¹ = (codeMat 122 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 460 : Mat3).transpose * (codeMat 122 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s7_actual_le_transport :
    o451ActualSourceSpan ⟨7, by omega⟩ ≤ actionW (codeMat 188) (codeMat 460) o196W := by
  apply o451_spanCodes_le_of_gens [257, 129, 100, 19, 10]
    (actionW (codeMat 188) (codeMat 460) o196W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 435 (by decide))
      (by unfold actionA; rw [o451d_s7_QtInv]; show (codeMat 188 : Mat3).transpose * codeMat 435 * (codeMat 122 : Mat3).transpose = codeMat 257; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 434 (by decide))
      (by unfold actionA; rw [o451d_s7_QtInv]; show (codeMat 188 : Mat3).transpose * codeMat 434 * (codeMat 122 : Mat3).transpose = codeMat 129; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 43 (by decide))
      (by unfold actionA; rw [o451d_s7_QtInv]; show (codeMat 188 : Mat3).transpose * codeMat 43 * (codeMat 122 : Mat3).transpose = codeMat 100; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 402 (by decide))
      (by unfold actionA; rw [o451d_s7_QtInv]; show (codeMat 188 : Mat3).transpose * codeMat 402 * (codeMat 122 : Mat3).transpose = codeMat 19; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 164 (by decide))
      (by unfold actionA; rw [o451d_s7_QtInv]; show (codeMat 188 : Mat3).transpose * codeMat 164 * (codeMat 122 : Mat3).transpose = codeMat 10; ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o451d_s7_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨7, by omega⟩) 16 :=
  quotientRankAtLeast_mono o451d_s7_actual_le_transport (o451_qra_action_code 188 460 (by decide) (by decide) step99_orbit196_lb16_unconditional)

private theorem o451d_s7_qra : QuotientRankAtLeast (o451SourceU ⟨7, by omega⟩) 16 :=
  quotientRankAtLeast_mono o451s7_sourceU_le_actual o451d_s7_qra_actual

-- Source 8: orbit 196, lb=16, action, P=172, Q=468, Qinv=87
private theorem o451d_s8_QtInv :
    (codeMat 468 : Mat3).transpose⁻¹ = (codeMat 87 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 468 : Mat3).transpose * (codeMat 87 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s8_actual_le_transport :
    o451ActualSourceSpan ⟨8, by omega⟩ ≤ actionW (codeMat 172) (codeMat 468) o196W := by
  apply o451_spanCodes_le_of_gens [257, 132, 65, 19, 10]
    (actionW (codeMat 172) (codeMat 468) o196W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 33 (by decide))
      (by unfold actionA; rw [o451d_s8_QtInv]; show (codeMat 172 : Mat3).transpose * codeMat 33 * (codeMat 87 : Mat3).transpose = codeMat 257; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 43 (by decide))
      (by unfold actionA; rw [o451d_s8_QtInv]; show (codeMat 172 : Mat3).transpose * codeMat 43 * (codeMat 87 : Mat3).transpose = codeMat 132; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 32 (by decide))
      (by unfold actionA; rw [o451d_s8_QtInv]; show (codeMat 172 : Mat3).transpose * codeMat 32 * (codeMat 87 : Mat3).transpose = codeMat 65; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 402 (by decide))
      (by unfold actionA; rw [o451d_s8_QtInv]; show (codeMat 172 : Mat3).transpose * codeMat 402 * (codeMat 87 : Mat3).transpose = codeMat 19; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 310 (by decide))
      (by unfold actionA; rw [o451d_s8_QtInv]; show (codeMat 172 : Mat3).transpose * codeMat 310 * (codeMat 87 : Mat3).transpose = codeMat 10; ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o451d_s8_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨8, by omega⟩) 16 :=
  quotientRankAtLeast_mono o451d_s8_actual_le_transport (o451_qra_action_code 172 468 (by decide) (by decide) step99_orbit196_lb16_unconditional)

private theorem o451d_s8_qra : QuotientRankAtLeast (o451SourceU ⟨8, by omega⟩) 16 :=
  quotientRankAtLeast_mono o451s8_sourceU_le_actual o451d_s8_qra_actual

-- Source 9: orbit 196, lb=16, action, P=236, Q=340, Qinv=85
private theorem o451d_s9_QtInv :
    (codeMat 340 : Mat3).transpose⁻¹ = (codeMat 85 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 340 : Mat3).transpose * (codeMat 85 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s9_actual_le_transport :
    o451ActualSourceSpan ⟨9, by omega⟩ ≤ actionW (codeMat 236) (codeMat 340) o196W := by
  apply o451_spanCodes_le_of_gens [257, 133, 65, 19, 10]
    (actionW (codeMat 236) (codeMat 340) o196W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 33 (by decide))
      (by unfold actionA; rw [o451d_s9_QtInv]; show (codeMat 236 : Mat3).transpose * codeMat 33 * (codeMat 85 : Mat3).transpose = codeMat 257; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 11 (by decide))
      (by unfold actionA; rw [o451d_s9_QtInv]; show (codeMat 236 : Mat3).transpose * codeMat 11 * (codeMat 85 : Mat3).transpose = codeMat 133; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 32 (by decide))
      (by unfold actionA; rw [o451d_s9_QtInv]; show (codeMat 236 : Mat3).transpose * codeMat 32 * (codeMat 85 : Mat3).transpose = codeMat 65; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 164 (by decide))
      (by unfold actionA; rw [o451d_s9_QtInv]; show (codeMat 236 : Mat3).transpose * codeMat 164 * (codeMat 85 : Mat3).transpose = codeMat 19; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 310 (by decide))
      (by unfold actionA; rw [o451d_s9_QtInv]; show (codeMat 236 : Mat3).transpose * codeMat 310 * (codeMat 85 : Mat3).transpose = codeMat 10; ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o451d_s9_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨9, by omega⟩) 16 :=
  quotientRankAtLeast_mono o451d_s9_actual_le_transport (o451_qra_action_code 236 340 (by decide) (by decide) step99_orbit196_lb16_unconditional)

private theorem o451d_s9_qra : QuotientRankAtLeast (o451SourceU ⟨9, by omega⟩) 16 :=
  quotientRankAtLeast_mono o451s9_sourceU_le_actual o451d_s9_qra_actual

-- Source 10: orbit 196, lb=16, transpose_after_action, P=188, Q=460, Qinv=122
private theorem o451d_s10_QtInv :
    (codeMat 460 : Mat3).transpose⁻¹ = (codeMat 122 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 460 : Mat3).transpose * (codeMat 122 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s10_actual_le_transport :
    o451ActualSourceSpan ⟨10, by omega⟩ ≤ transposeW (actionW (codeMat 188) (codeMat 460) o196W) := by
  apply o451_spanCodes_le_of_gens [257, 196, 33, 19, 10]
    (transposeW (actionW (codeMat 188) (codeMat 460) o196W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    exact ⟨codeMat 257,
      o451_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 435 (by decide))
        (by unfold actionA; rw [o451d_s10_QtInv]; show (codeMat 188 : Mat3).transpose * codeMat 435 * (codeMat 122 : Mat3).transpose = codeMat 257; ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h1
    exact ⟨codeMat 100,
      o451_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 43 (by decide))
        (by unfold actionA; rw [o451d_s10_QtInv]; show (codeMat 188 : Mat3).transpose * codeMat 43 * (codeMat 122 : Mat3).transpose = codeMat 100; ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h2
    exact ⟨codeMat 129,
      o451_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 434 (by decide))
        (by unfold actionA; rw [o451d_s10_QtInv]; show (codeMat 188 : Mat3).transpose * codeMat 434 * (codeMat 122 : Mat3).transpose = codeMat 129; ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h3
    exact ⟨codeMat 25,
      o451_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 310 (by decide))
        (by unfold actionA; rw [o451d_s10_QtInv]; show (codeMat 188 : Mat3).transpose * codeMat 310 * (codeMat 122 : Mat3).transpose = codeMat 25; ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h4
    exact ⟨codeMat 10,
      o451_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 164 (by decide))
        (by unfold actionA; rw [o451d_s10_QtInv]; show (codeMat 188 : Mat3).transpose * codeMat 164 * (codeMat 122 : Mat3).transpose = codeMat 10; ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩

private theorem o451d_s10_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨10, by omega⟩) 16 :=
  quotientRankAtLeast_mono o451d_s10_actual_le_transport (quotientRankAtLeast_transpose (o451_qra_action_code 188 460 (by decide) (by decide) step99_orbit196_lb16_unconditional))

private theorem o451d_s10_qra : QuotientRankAtLeast (o451SourceU ⟨10, by omega⟩) 16 :=
  quotientRankAtLeast_mono o451s10_sourceU_le_actual o451d_s10_qra_actual

-- Source 11: orbit 196, lb=16, transpose_after_action, P=244, Q=348, Qinv=125
private theorem o451d_s11_QtInv :
    (codeMat 348 : Mat3).transpose⁻¹ = (codeMat 125 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 348 : Mat3).transpose * (codeMat 125 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s11_actual_le_transport :
    o451ActualSourceSpan ⟨11, by omega⟩ ≤ transposeW (actionW (codeMat 244) (codeMat 348) o196W) := by
  apply o451_spanCodes_le_of_gens [257, 132, 37, 19, 10]
    (transposeW (actionW (codeMat 244) (codeMat 348) o196W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    exact ⟨codeMat 257,
      o451_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 435 (by decide))
        (by unfold actionA; rw [o451d_s11_QtInv]; show (codeMat 244 : Mat3).transpose * codeMat 435 * (codeMat 125 : Mat3).transpose = codeMat 257; ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h1
    exact ⟨codeMat 96,
      o451_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 43 (by decide))
        (by unfold actionA; rw [o451d_s11_QtInv]; show (codeMat 244 : Mat3).transpose * codeMat 43 * (codeMat 125 : Mat3).transpose = codeMat 96; ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h2
    exact ⟨codeMat 193,
      o451_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 434 (by decide))
        (by unfold actionA; rw [o451d_s11_QtInv]; show (codeMat 244 : Mat3).transpose * codeMat 434 * (codeMat 125 : Mat3).transpose = codeMat 193; ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h3
    exact ⟨codeMat 25,
      o451_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 402 (by decide))
        (by unfold actionA; rw [o451d_s11_QtInv]; show (codeMat 244 : Mat3).transpose * codeMat 402 * (codeMat 125 : Mat3).transpose = codeMat 25; ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h4
    exact ⟨codeMat 10,
      o451_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 164 (by decide))
        (by unfold actionA; rw [o451d_s11_QtInv]; show (codeMat 244 : Mat3).transpose * codeMat 164 * (codeMat 125 : Mat3).transpose = codeMat 10; ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩

private theorem o451d_s11_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨11, by omega⟩) 16 :=
  quotientRankAtLeast_mono o451d_s11_actual_le_transport (quotientRankAtLeast_transpose (o451_qra_action_code 244 348 (by decide) (by decide) step99_orbit196_lb16_unconditional))

private theorem o451d_s11_qra : QuotientRankAtLeast (o451SourceU ⟨11, by omega⟩) 16 :=
  quotientRankAtLeast_mono o451s11_sourceU_le_actual o451d_s11_qra_actual

-- Source 12: orbit 196, lb=16, transpose_after_action, P=172, Q=468, Qinv=87
private theorem o451d_s12_QtInv :
    (codeMat 468 : Mat3).transpose⁻¹ = (codeMat 87 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 468 : Mat3).transpose * (codeMat 87 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s12_actual_le_transport :
    o451ActualSourceSpan ⟨12, by omega⟩ ≤ transposeW (actionW (codeMat 172) (codeMat 468) o196W) := by
  apply o451_spanCodes_le_of_gens [257, 96, 19, 10, 5]
    (transposeW (actionW (codeMat 172) (codeMat 468) o196W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    exact ⟨codeMat 257,
      o451_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 33 (by decide))
        (by unfold actionA; rw [o451d_s12_QtInv]; show (codeMat 172 : Mat3).transpose * codeMat 33 * (codeMat 87 : Mat3).transpose = codeMat 257; ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h1
    exact ⟨codeMat 132,
      o451_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 43 (by decide))
        (by unfold actionA; rw [o451d_s12_QtInv]; show (codeMat 172 : Mat3).transpose * codeMat 43 * (codeMat 87 : Mat3).transpose = codeMat 132; ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h2
    exact ⟨codeMat 25,
      o451_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 164 (by decide))
        (by unfold actionA; rw [o451d_s12_QtInv]; show (codeMat 172 : Mat3).transpose * codeMat 164 * (codeMat 87 : Mat3).transpose = codeMat 25; ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h3
    exact ⟨codeMat 10,
      o451_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 310 (by decide))
        (by unfold actionA; rw [o451d_s12_QtInv]; show (codeMat 172 : Mat3).transpose * codeMat 310 * (codeMat 87 : Mat3).transpose = codeMat 10; ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h4
    exact ⟨codeMat 65,
      o451_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 32 (by decide))
        (by unfold actionA; rw [o451d_s12_QtInv]; show (codeMat 172 : Mat3).transpose * codeMat 32 * (codeMat 87 : Mat3).transpose = codeMat 65; ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩

private theorem o451d_s12_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨12, by omega⟩) 16 :=
  quotientRankAtLeast_mono o451d_s12_actual_le_transport (quotientRankAtLeast_transpose (o451_qra_action_code 172 468 (by decide) (by decide) step99_orbit196_lb16_unconditional))

private theorem o451d_s12_qra : QuotientRankAtLeast (o451SourceU ⟨12, by omega⟩) 16 :=
  quotientRankAtLeast_mono o451s12_sourceU_le_actual o451d_s12_qra_actual

-- Source 13: orbit 196, lb=16, transpose_after_action, P=236, Q=340, Qinv=85
private theorem o451d_s13_QtInv :
    (codeMat 340 : Mat3).transpose⁻¹ = (codeMat 85 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 340 : Mat3).transpose * (codeMat 85 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s13_actual_le_transport :
    o451ActualSourceSpan ⟨13, by omega⟩ ≤ transposeW (actionW (codeMat 236) (codeMat 340) o196W) := by
  apply o451_spanCodes_le_of_gens [257, 97, 19, 10, 5]
    (transposeW (actionW (codeMat 236) (codeMat 340) o196W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    exact ⟨codeMat 257,
      o451_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 33 (by decide))
        (by unfold actionA; rw [o451d_s13_QtInv]; show (codeMat 236 : Mat3).transpose * codeMat 33 * (codeMat 85 : Mat3).transpose = codeMat 257; ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h1
    exact ⟨codeMat 133,
      o451_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 11 (by decide))
        (by unfold actionA; rw [o451d_s13_QtInv]; show (codeMat 236 : Mat3).transpose * codeMat 11 * (codeMat 85 : Mat3).transpose = codeMat 133; ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h2
    exact ⟨codeMat 25,
      o451_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 402 (by decide))
        (by unfold actionA; rw [o451d_s13_QtInv]; show (codeMat 236 : Mat3).transpose * codeMat 402 * (codeMat 85 : Mat3).transpose = codeMat 25; ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h3
    exact ⟨codeMat 10,
      o451_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 310 (by decide))
        (by unfold actionA; rw [o451d_s13_QtInv]; show (codeMat 236 : Mat3).transpose * codeMat 310 * (codeMat 85 : Mat3).transpose = codeMat 10; ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h4
    exact ⟨codeMat 65,
      o451_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 32 (by decide))
        (by unfold actionA; rw [o451d_s13_QtInv]; show (codeMat 236 : Mat3).transpose * codeMat 32 * (codeMat 85 : Mat3).transpose = codeMat 65; ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩

private theorem o451d_s13_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨13, by omega⟩) 16 :=
  quotientRankAtLeast_mono o451d_s13_actual_le_transport (quotientRankAtLeast_transpose (o451_qra_action_code 236 340 (by decide) (by decide) step99_orbit196_lb16_unconditional))

private theorem o451d_s13_qra : QuotientRankAtLeast (o451SourceU ⟨13, by omega⟩) 16 :=
  quotientRankAtLeast_mono o451s13_sourceU_le_actual o451d_s13_qra_actual

-- Source 14: orbit 31, lb=15, transpose_after_action, P=266, Q=140, Qinv=98
private theorem o451d_s14_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s14_actual_le_transport :
    o451ActualSourceSpan ⟨14, by omega⟩ ≤ transposeW (actionW (codeMat 266) (codeMat 140) orbit31W) := by
  apply o451_spanCodes_le_of_gens [257, 128, 64, 17, 8, 2]
    (transposeW (actionW (codeMat 266) (codeMat 140) orbit31W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact ⟨codeMat 257,
      o451_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 80 (by decide))
        (by unfold actionA; rw [o451d_s14_QtInv]; show (codeMat 266 : Mat3).transpose * codeMat 80 * (codeMat 98 : Mat3).transpose = codeMat 257; ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h1
    exact ⟨codeMat 32,
      o451_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 1 (by decide))
        (by unfold actionA; rw [o451d_s14_QtInv]; show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 32; ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h2
    exact ⟨codeMat 4,
      o451_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 8 (by decide))
        (by unfold actionA; rw [o451d_s14_QtInv]; show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 4; ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h3
    exact ⟨codeMat 17,
      o451_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 20 (by decide))
        (by unfold actionA; rw [o451d_s14_QtInv]; show (codeMat 266 : Mat3).transpose * codeMat 20 * (codeMat 98 : Mat3).transpose = codeMat 17; ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h4
    exact ⟨codeMat 2,
      o451_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 32 (by decide))
        (by unfold actionA; rw [o451d_s14_QtInv]; show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 98 : Mat3).transpose = codeMat 2; ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h5
    exact ⟨codeMat 8,
      o451_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 2 (by decide))
        (by unfold actionA; rw [o451d_s14_QtInv]; show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 98 : Mat3).transpose = codeMat 8; ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩

private theorem o451d_s14_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨14, by omega⟩) 15 :=
  quotientRankAtLeast_mono o451d_s14_actual_le_transport (quotientRankAtLeast_transpose (o451_qra_action_code 266 140 (by decide) (by decide) orbit31_lb15))

private theorem o451d_s14_qra : QuotientRankAtLeast (o451SourceU ⟨14, by omega⟩) 15 :=
  quotientRankAtLeast_mono o451s14_sourceU_le_actual o451d_s14_qra_actual

-- Source 15: orbit 31, lb=15, transpose_after_action, P=266, Q=92, Qinv=116
private theorem o451d_s15_QtInv :
    (codeMat 92 : Mat3).transpose⁻¹ = (codeMat 116 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 92 : Mat3).transpose * (codeMat 116 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s15_actual_le_transport :
    o451ActualSourceSpan ⟨15, by omega⟩ ≤ transposeW (actionW (codeMat 266) (codeMat 92) orbit31W) := by
  apply o451_spanCodes_le_of_gens [257, 128, 64, 16, 9, 3]
    (transposeW (actionW (codeMat 266) (codeMat 92) orbit31W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact ⟨codeMat 257,
      o451_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 112 (by decide))
        (by unfold actionA; rw [o451d_s15_QtInv]; show (codeMat 266 : Mat3).transpose * codeMat 112 * (codeMat 116 : Mat3).transpose = codeMat 257; ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h1
    exact ⟨codeMat 32,
      o451_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 1 (by decide))
        (by unfold actionA; rw [o451d_s15_QtInv]; show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 116 : Mat3).transpose = codeMat 32; ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h2
    exact ⟨codeMat 4,
      o451_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 8 (by decide))
        (by unfold actionA; rw [o451d_s15_QtInv]; show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 116 : Mat3).transpose = codeMat 4; ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h3
    exact ⟨codeMat 16,
      o451_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 2 (by decide))
        (by unfold actionA; rw [o451d_s15_QtInv]; show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 116 : Mat3).transpose = codeMat 16; ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h4
    exact ⟨codeMat 3,
      o451_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 32 (by decide))
        (by unfold actionA; rw [o451d_s15_QtInv]; show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 116 : Mat3).transpose = codeMat 3; ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h5
    exact ⟨codeMat 9,
      o451_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 54 (by decide))
        (by unfold actionA; rw [o451d_s15_QtInv]; show (codeMat 266 : Mat3).transpose * codeMat 54 * (codeMat 116 : Mat3).transpose = codeMat 9; ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩

private theorem o451d_s15_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨15, by omega⟩) 15 :=
  quotientRankAtLeast_mono o451d_s15_actual_le_transport (quotientRankAtLeast_transpose (o451_qra_action_code 266 92 (by decide) (by decide) orbit31_lb15))

private theorem o451d_s15_qra : QuotientRankAtLeast (o451SourceU ⟨15, by omega⟩) 15 :=
  quotientRankAtLeast_mono o451s15_sourceU_le_actual o451d_s15_qra_actual

-- Source 16: orbit 65, lb=15, action, P=99, Q=99, Qinv=172
private theorem o451d_s16_QtInv :
    (codeMat 99 : Mat3).transpose⁻¹ = (codeMat 172 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 99 : Mat3).transpose * (codeMat 172 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s16_actual_le_transport :
    o451ActualSourceSpan ⟨16, by omega⟩ ≤ actionW (codeMat 99) (codeMat 99) o65W := by
  apply o451_spanCodes_le_of_gens [256, 164, 96, 18, 10, 1]
    (actionW (codeMat 99) (codeMat 99) o65W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 16 (by decide))
      (by unfold actionA; rw [o451d_s16_QtInv]; show (codeMat 99 : Mat3).transpose * codeMat 16 * (codeMat 172 : Mat3).transpose = codeMat 256; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 10 (by decide))
      (by unfold actionA; rw [o451d_s16_QtInv]; show (codeMat 99 : Mat3).transpose * codeMat 10 * (codeMat 172 : Mat3).transpose = codeMat 164; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 170 (by decide))
      (by unfold actionA; rw [o451d_s16_QtInv]; show (codeMat 99 : Mat3).transpose * codeMat 170 * (codeMat 172 : Mat3).transpose = codeMat 96; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 1 (by decide))
      (by unfold actionA; rw [o451d_s16_QtInv]; show (codeMat 99 : Mat3).transpose * codeMat 1 * (codeMat 172 : Mat3).transpose = codeMat 18; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 261 (by decide))
      (by unfold actionA; rw [o451d_s16_QtInv]; show (codeMat 99 : Mat3).transpose * codeMat 261 * (codeMat 172 : Mat3).transpose = codeMat 10; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 320 (by decide))
      (by unfold actionA; rw [o451d_s16_QtInv]; show (codeMat 99 : Mat3).transpose * codeMat 320 * (codeMat 172 : Mat3).transpose = codeMat 1; ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o451d_s16_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨16, by omega⟩) 15 :=
  quotientRankAtLeast_mono o451d_s16_actual_le_transport (o451_qra_action_code 99 99 (by decide) (by decide) step99_orbit65_lb15_unconditional)

private theorem o451d_s16_qra : QuotientRankAtLeast (o451SourceU ⟨16, by omega⟩) 15 :=
  quotientRankAtLeast_mono o451s16_sourceU_le_actual o451d_s16_qra_actual

-- Source 17: orbit 65, lb=15, action, P=98, Q=225, Qinv=169
private theorem o451d_s17_QtInv :
    (codeMat 225 : Mat3).transpose⁻¹ = (codeMat 169 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 225 : Mat3).transpose * (codeMat 169 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s17_actual_le_transport :
    o451ActualSourceSpan ⟨17, by omega⟩ ≤ actionW (codeMat 98) (codeMat 225) o65W := by
  apply o451_spanCodes_le_of_gens [256, 132, 100, 18, 10, 1]
    (actionW (codeMat 98) (codeMat 225) o65W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 16 (by decide))
      (by unfold actionA; rw [o451d_s17_QtInv]; show (codeMat 98 : Mat3).transpose * codeMat 16 * (codeMat 169 : Mat3).transpose = codeMat 256; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 160 (by decide))
      (by unfold actionA; rw [o451d_s17_QtInv]; show (codeMat 98 : Mat3).transpose * codeMat 160 * (codeMat 169 : Mat3).transpose = codeMat 132; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 170 (by decide))
      (by unfold actionA; rw [o451d_s17_QtInv]; show (codeMat 98 : Mat3).transpose * codeMat 170 * (codeMat 169 : Mat3).transpose = codeMat 100; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 260 (by decide))
      (by unfold actionA; rw [o451d_s17_QtInv]; show (codeMat 98 : Mat3).transpose * codeMat 260 * (codeMat 169 : Mat3).transpose = codeMat 18; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 261 (by decide))
      (by unfold actionA; rw [o451d_s17_QtInv]; show (codeMat 98 : Mat3).transpose * codeMat 261 * (codeMat 169 : Mat3).transpose = codeMat 10; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 320 (by decide))
      (by unfold actionA; rw [o451d_s17_QtInv]; show (codeMat 98 : Mat3).transpose * codeMat 320 * (codeMat 169 : Mat3).transpose = codeMat 1; ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o451d_s17_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨17, by omega⟩) 15 :=
  quotientRankAtLeast_mono o451d_s17_actual_le_transport (o451_qra_action_code 98 225 (by decide) (by decide) step99_orbit65_lb15_unconditional)

private theorem o451d_s17_qra : QuotientRankAtLeast (o451SourceU ⟨17, by omega⟩) 15 :=
  quotientRankAtLeast_mono o451s17_sourceU_le_actual o451d_s17_qra_actual

-- Source 18: orbit 31, lb=15, action, P=266, Q=140, Qinv=98
private theorem o451d_s18_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s18_actual_le_transport :
    o451ActualSourceSpan ⟨18, by omega⟩ ≤ actionW (codeMat 266) (codeMat 140) orbit31W := by
  apply o451_spanCodes_le_of_gens [257, 32, 17, 8, 4, 2]
    (actionW (codeMat 266) (codeMat 140) orbit31W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 80 (by decide))
      (by unfold actionA; rw [o451d_s18_QtInv]; show (codeMat 266 : Mat3).transpose * codeMat 80 * (codeMat 98 : Mat3).transpose = codeMat 257; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 1 (by decide))
      (by unfold actionA; rw [o451d_s18_QtInv]; show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 32; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 20 (by decide))
      (by unfold actionA; rw [o451d_s18_QtInv]; show (codeMat 266 : Mat3).transpose * codeMat 20 * (codeMat 98 : Mat3).transpose = codeMat 17; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 2 (by decide))
      (by unfold actionA; rw [o451d_s18_QtInv]; show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 98 : Mat3).transpose = codeMat 8; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 8 (by decide))
      (by unfold actionA; rw [o451d_s18_QtInv]; show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 4; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 32 (by decide))
      (by unfold actionA; rw [o451d_s18_QtInv]; show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 98 : Mat3).transpose = codeMat 2; ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o451d_s18_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨18, by omega⟩) 15 :=
  quotientRankAtLeast_mono o451d_s18_actual_le_transport (o451_qra_action_code 266 140 (by decide) (by decide) orbit31_lb15)

private theorem o451d_s18_qra : QuotientRankAtLeast (o451SourceU ⟨18, by omega⟩) 15 :=
  quotientRankAtLeast_mono o451s18_sourceU_le_actual o451d_s18_qra_actual

-- Source 19: orbit 31, lb=15, action, P=266, Q=92, Qinv=116
private theorem o451d_s19_QtInv :
    (codeMat 92 : Mat3).transpose⁻¹ = (codeMat 116 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 92 : Mat3).transpose * (codeMat 116 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s19_actual_le_transport :
    o451ActualSourceSpan ⟨19, by omega⟩ ≤ actionW (codeMat 266) (codeMat 92) orbit31W := by
  apply o451_spanCodes_le_of_gens [257, 32, 16, 9, 4, 3]
    (actionW (codeMat 266) (codeMat 92) orbit31W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 112 (by decide))
      (by unfold actionA; rw [o451d_s19_QtInv]; show (codeMat 266 : Mat3).transpose * codeMat 112 * (codeMat 116 : Mat3).transpose = codeMat 257; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 1 (by decide))
      (by unfold actionA; rw [o451d_s19_QtInv]; show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 116 : Mat3).transpose = codeMat 32; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 2 (by decide))
      (by unfold actionA; rw [o451d_s19_QtInv]; show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 116 : Mat3).transpose = codeMat 16; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 54 (by decide))
      (by unfold actionA; rw [o451d_s19_QtInv]; show (codeMat 266 : Mat3).transpose * codeMat 54 * (codeMat 116 : Mat3).transpose = codeMat 9; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 8 (by decide))
      (by unfold actionA; rw [o451d_s19_QtInv]; show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 116 : Mat3).transpose = codeMat 4; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 32 (by decide))
      (by unfold actionA; rw [o451d_s19_QtInv]; show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 116 : Mat3).transpose = codeMat 3; ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o451d_s19_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨19, by omega⟩) 15 :=
  quotientRankAtLeast_mono o451d_s19_actual_le_transport (o451_qra_action_code 266 92 (by decide) (by decide) orbit31_lb15)

private theorem o451d_s19_qra : QuotientRankAtLeast (o451SourceU ⟨19, by omega⟩) 15 :=
  quotientRankAtLeast_mono o451s19_sourceU_le_actual o451d_s19_qra_actual

-- Source 20: orbit 17, lb=14, action, P=87, Q=106, Qinv=396
private theorem o451d_s20_QtInv :
    (codeMat 106 : Mat3).transpose⁻¹ = (codeMat 396 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 106 : Mat3).transpose * (codeMat 396 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s20_actual_le_transport :
    o451ActualSourceSpan ⟨20, by omega⟩ ≤ actionW (codeMat 87) (codeMat 106) step81o17s4Wspan := by
  apply o451_spanCodes_le_of_gens [257, 129, 66, 34, 19, 10, 4]
    (actionW (codeMat 87) (codeMat 106) step81o17s4Wspan)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 274 (by decide))
      (by unfold actionA; rw [o451d_s20_QtInv]; show (codeMat 87 : Mat3).transpose * codeMat 274 * (codeMat 396 : Mat3).transpose = codeMat 257; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 457 (by decide))
      (by unfold actionA; rw [o451d_s20_QtInv]; show (codeMat 87 : Mat3).transpose * codeMat 457 * (codeMat 396 : Mat3).transpose = codeMat 129; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 502 (by decide))
      (by unfold actionA; rw [o451d_s20_QtInv]; show (codeMat 87 : Mat3).transpose * codeMat 502 * (codeMat 396 : Mat3).transpose = codeMat 66; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 80 (by decide))
      (by unfold actionA; rw [o451d_s20_QtInv]; show (codeMat 87 : Mat3).transpose * codeMat 80 * (codeMat 396 : Mat3).transpose = codeMat 34; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 456 (by decide))
      (by unfold actionA; rw [o451d_s20_QtInv]; show (codeMat 87 : Mat3).transpose * codeMat 456 * (codeMat 396 : Mat3).transpose = codeMat 19; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 112 (by decide))
      (by unfold actionA; rw [o451d_s20_QtInv]; show (codeMat 87 : Mat3).transpose * codeMat 112 * (codeMat 396 : Mat3).transpose = codeMat 10; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h6
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 128 (by decide))
      (by unfold actionA; rw [o451d_s20_QtInv]; show (codeMat 87 : Mat3).transpose * codeMat 128 * (codeMat 396 : Mat3).transpose = codeMat 4; ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o451d_s20_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨20, by omega⟩) 14 :=
  quotientRankAtLeast_mono o451d_s20_actual_le_transport (o451_qra_action_code 87 106 (by decide) (by decide) step81o17s4Span_lb)

private theorem o451d_s20_qra : QuotientRankAtLeast (o451SourceU ⟨20, by omega⟩) 14 :=
  quotientRankAtLeast_mono o451s20_sourceU_le_actual o451d_s20_qra_actual

-- Source 21: orbit 17, lb=14, action, P=94, Q=250, Qinv=397
private theorem o451d_s21_QtInv :
    (codeMat 250 : Mat3).transpose⁻¹ = (codeMat 397 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 250 : Mat3).transpose * (codeMat 397 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s21_actual_le_transport :
    o451ActualSourceSpan ⟨21, by omega⟩ ≤ actionW (codeMat 94) (codeMat 250) step81o17s4Wspan := by
  apply o451_spanCodes_le_of_gens [257, 130, 67, 35, 19, 10, 4]
    (actionW (codeMat 94) (codeMat 250) step81o17s4Wspan)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 274 (by decide))
      (by unfold actionA; rw [o451d_s21_QtInv]; show (codeMat 94 : Mat3).transpose * codeMat 274 * (codeMat 397 : Mat3).transpose = codeMat 257; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 63 (by decide))
      (by unfold actionA; rw [o451d_s21_QtInv]; show (codeMat 94 : Mat3).transpose * codeMat 63 * (codeMat 397 : Mat3).transpose = codeMat 130; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 502 (by decide))
      (by unfold actionA; rw [o451d_s21_QtInv]; show (codeMat 94 : Mat3).transpose * codeMat 502 * (codeMat 397 : Mat3).transpose = codeMat 67; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 208 (by decide))
      (by unfold actionA; rw [o451d_s21_QtInv]; show (codeMat 94 : Mat3).transpose * codeMat 208 * (codeMat 397 : Mat3).transpose = codeMat 35; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 440 (by decide))
      (by unfold actionA; rw [o451d_s21_QtInv]; show (codeMat 94 : Mat3).transpose * codeMat 440 * (codeMat 397 : Mat3).transpose = codeMat 19; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 112 (by decide))
      (by unfold actionA; rw [o451d_s21_QtInv]; show (codeMat 94 : Mat3).transpose * codeMat 112 * (codeMat 397 : Mat3).transpose = codeMat 10; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h6
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 128 (by decide))
      (by unfold actionA; rw [o451d_s21_QtInv]; show (codeMat 94 : Mat3).transpose * codeMat 128 * (codeMat 397 : Mat3).transpose = codeMat 4; ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o451d_s21_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨21, by omega⟩) 14 :=
  quotientRankAtLeast_mono o451d_s21_actual_le_transport (o451_qra_action_code 94 250 (by decide) (by decide) step81o17s4Span_lb)

private theorem o451d_s21_qra : QuotientRankAtLeast (o451SourceU ⟨21, by omega⟩) 14 :=
  quotientRankAtLeast_mono o451s21_sourceU_le_actual o451d_s21_qra_actual

-- Source 22: orbit 17, lb=14, action, P=87, Q=473, Qinv=409
private theorem o451d_s22_QtInv :
    (codeMat 473 : Mat3).transpose⁻¹ = (codeMat 409 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 473 : Mat3).transpose * (codeMat 409 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s22_actual_le_transport :
    o451ActualSourceSpan ⟨22, by omega⟩ ≤ actionW (codeMat 87) (codeMat 473) step81o17s4Wspan := by
  apply o451_spanCodes_le_of_gens [257, 131, 65, 32, 19, 10, 6]
    (actionW (codeMat 87) (codeMat 473) step81o17s4Wspan)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 228 (by decide))
      (by unfold actionA; rw [o451d_s22_QtInv]; show (codeMat 87 : Mat3).transpose * codeMat 228 * (codeMat 409 : Mat3).transpose = codeMat 257; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 502 (by decide))
      (by unfold actionA; rw [o451d_s22_QtInv]; show (codeMat 87 : Mat3).transpose * codeMat 502 * (codeMat 409 : Mat3).transpose = codeMat 131; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 63 (by decide))
      (by unfold actionA; rw [o451d_s22_QtInv]; show (codeMat 87 : Mat3).transpose * codeMat 63 * (codeMat 409 : Mat3).transpose = codeMat 65; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 32 (by decide))
      (by unfold actionA; rw [o451d_s22_QtInv]; show (codeMat 87 : Mat3).transpose * codeMat 32 * (codeMat 409 : Mat3).transpose = codeMat 32; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 112 (by decide))
      (by unfold actionA; rw [o451d_s22_QtInv]; show (codeMat 87 : Mat3).transpose * codeMat 112 * (codeMat 409 : Mat3).transpose = codeMat 19; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 440 (by decide))
      (by unfold actionA; rw [o451d_s22_QtInv]; show (codeMat 87 : Mat3).transpose * codeMat 440 * (codeMat 409 : Mat3).transpose = codeMat 10; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h6
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 128 (by decide))
      (by unfold actionA; rw [o451d_s22_QtInv]; show (codeMat 87 : Mat3).transpose * codeMat 128 * (codeMat 409 : Mat3).transpose = codeMat 6; ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o451d_s22_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨22, by omega⟩) 14 :=
  quotientRankAtLeast_mono o451d_s22_actual_le_transport (o451_qra_action_code 87 473 (by decide) (by decide) step81o17s4Span_lb)

private theorem o451d_s22_qra : QuotientRankAtLeast (o451SourceU ⟨22, by omega⟩) 14 :=
  quotientRankAtLeast_mono o451s22_sourceU_le_actual o451d_s22_qra_actual

-- Source 23: orbit 17, lb=14, action, P=87, Q=407, Qinv=405
private theorem o451d_s23_QtInv :
    (codeMat 407 : Mat3).transpose⁻¹ = (codeMat 405 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 407 : Mat3).transpose * (codeMat 405 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s23_actual_le_transport :
    o451ActualSourceSpan ⟨23, by omega⟩ ≤ actionW (codeMat 87) (codeMat 407) step81o17s4Wspan := by
  apply o451_spanCodes_le_of_gens [257, 130, 67, 34, 19, 10, 6]
    (actionW (codeMat 87) (codeMat 407) step81o17s4Wspan)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 301 (by decide))
      (by unfold actionA; rw [o451d_s23_QtInv]; show (codeMat 87 : Mat3).transpose * codeMat 301 * (codeMat 405 : Mat3).transpose = codeMat 257; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 63 (by decide))
      (by unfold actionA; rw [o451d_s23_QtInv]; show (codeMat 87 : Mat3).transpose * codeMat 63 * (codeMat 405 : Mat3).transpose = codeMat 130; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 457 (by decide))
      (by unfold actionA; rw [o451d_s23_QtInv]; show (codeMat 87 : Mat3).transpose * codeMat 457 * (codeMat 405 : Mat3).transpose = codeMat 67; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 488 (by decide))
      (by unfold actionA; rw [o451d_s23_QtInv]; show (codeMat 87 : Mat3).transpose * codeMat 488 * (codeMat 405 : Mat3).transpose = codeMat 34; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 440 (by decide))
      (by unfold actionA; rw [o451d_s23_QtInv]; show (codeMat 87 : Mat3).transpose * codeMat 440 * (codeMat 405 : Mat3).transpose = codeMat 19; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 456 (by decide))
      (by unfold actionA; rw [o451d_s23_QtInv]; show (codeMat 87 : Mat3).transpose * codeMat 456 * (codeMat 405 : Mat3).transpose = codeMat 10; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h6
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 128 (by decide))
      (by unfold actionA; rw [o451d_s23_QtInv]; show (codeMat 87 : Mat3).transpose * codeMat 128 * (codeMat 405 : Mat3).transpose = codeMat 6; ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o451d_s23_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨23, by omega⟩) 14 :=
  quotientRankAtLeast_mono o451d_s23_actual_le_transport (o451_qra_action_code 87 407 (by decide) (by decide) step81o17s4Span_lb)

private theorem o451d_s23_qra : QuotientRankAtLeast (o451SourceU ⟨23, by omega⟩) 14 :=
  quotientRankAtLeast_mono o451s23_sourceU_le_actual o451d_s23_qra_actual

-- Source 24: orbit 17, lb=14, action, P=85, Q=110, Qinv=444
private theorem o451d_s24_QtInv :
    (codeMat 110 : Mat3).transpose⁻¹ = (codeMat 444 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 110 : Mat3).transpose * (codeMat 444 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s24_actual_le_transport :
    o451ActualSourceSpan ⟨24, by omega⟩ ≤ actionW (codeMat 85) (codeMat 110) step81o17s4Wspan := by
  apply o451_spanCodes_le_of_gens [257, 130, 64, 33, 19, 10, 6]
    (actionW (codeMat 85) (codeMat 110) step81o17s4Wspan)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 323 (by decide))
      (by unfold actionA; rw [o451d_s24_QtInv]; show (codeMat 85 : Mat3).transpose * codeMat 323 * (codeMat 444 : Mat3).transpose = codeMat 257; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 1 (by decide))
      (by unfold actionA; rw [o451d_s24_QtInv]; show (codeMat 85 : Mat3).transpose * codeMat 1 * (codeMat 444 : Mat3).transpose = codeMat 130; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 390 (by decide))
      (by unfold actionA; rw [o451d_s24_QtInv]; show (codeMat 85 : Mat3).transpose * codeMat 390 * (codeMat 444 : Mat3).transpose = codeMat 64; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 408 (by decide))
      (by unfold actionA; rw [o451d_s24_QtInv]; show (codeMat 85 : Mat3).transpose * codeMat 408 * (codeMat 444 : Mat3).transpose = codeMat 33; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 456 (by decide))
      (by unfold actionA; rw [o451d_s24_QtInv]; show (codeMat 85 : Mat3).transpose * codeMat 456 * (codeMat 444 : Mat3).transpose = codeMat 19; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 112 (by decide))
      (by unfold actionA; rw [o451d_s24_QtInv]; show (codeMat 85 : Mat3).transpose * codeMat 112 * (codeMat 444 : Mat3).transpose = codeMat 10; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h6
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 128 (by decide))
      (by unfold actionA; rw [o451d_s24_QtInv]; show (codeMat 85 : Mat3).transpose * codeMat 128 * (codeMat 444 : Mat3).transpose = codeMat 6; ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o451d_s24_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨24, by omega⟩) 14 :=
  quotientRankAtLeast_mono o451d_s24_actual_le_transport (o451_qra_action_code 85 110 (by decide) (by decide) step81o17s4Span_lb)

private theorem o451d_s24_qra : QuotientRankAtLeast (o451SourceU ⟨24, by omega⟩) 14 :=
  quotientRankAtLeast_mono o451s24_sourceU_le_actual o451d_s24_qra_actual

-- Source 25: orbit 17, lb=14, action, P=92, Q=111, Qinv=412
private theorem o451d_s25_QtInv :
    (codeMat 111 : Mat3).transpose⁻¹ = (codeMat 412 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 111 : Mat3).transpose * (codeMat 412 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s25_actual_le_transport :
    o451ActualSourceSpan ⟨25, by omega⟩ ≤ actionW (codeMat 92) (codeMat 111) step81o17s4Wspan := by
  apply o451_spanCodes_le_of_gens [257, 128, 67, 33, 19, 10, 6]
    (actionW (codeMat 92) (codeMat 111) step81o17s4Wspan)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 451 (by decide))
      (by unfold actionA; rw [o451d_s25_QtInv]; show (codeMat 92 : Mat3).transpose * codeMat 451 * (codeMat 412 : Mat3).transpose = codeMat 257; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 1 (by decide))
      (by unfold actionA; rw [o451d_s25_QtInv]; show (codeMat 92 : Mat3).transpose * codeMat 1 * (codeMat 412 : Mat3).transpose = codeMat 128; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 391 (by decide))
      (by unfold actionA; rw [o451d_s25_QtInv]; show (codeMat 92 : Mat3).transpose * codeMat 391 * (codeMat 412 : Mat3).transpose = codeMat 67; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 280 (by decide))
      (by unfold actionA; rw [o451d_s25_QtInv]; show (codeMat 92 : Mat3).transpose * codeMat 280 * (codeMat 412 : Mat3).transpose = codeMat 33; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 456 (by decide))
      (by unfold actionA; rw [o451d_s25_QtInv]; show (codeMat 92 : Mat3).transpose * codeMat 456 * (codeMat 412 : Mat3).transpose = codeMat 19; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 440 (by decide))
      (by unfold actionA; rw [o451d_s25_QtInv]; show (codeMat 92 : Mat3).transpose * codeMat 440 * (codeMat 412 : Mat3).transpose = codeMat 10; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h6
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 128 (by decide))
      (by unfold actionA; rw [o451d_s25_QtInv]; show (codeMat 92 : Mat3).transpose * codeMat 128 * (codeMat 412 : Mat3).transpose = codeMat 6; ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o451d_s25_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨25, by omega⟩) 14 :=
  quotientRankAtLeast_mono o451d_s25_actual_le_transport (o451_qra_action_code 92 111 (by decide) (by decide) step81o17s4Span_lb)

private theorem o451d_s25_qra : QuotientRankAtLeast (o451SourceU ⟨25, by omega⟩) 14 :=
  quotientRankAtLeast_mono o451s25_sourceU_le_actual o451d_s25_qra_actual

-- Source 26: orbit 17, lb=14, action, P=95, Q=181, Qinv=423
private theorem o451d_s26_QtInv :
    (codeMat 181 : Mat3).transpose⁻¹ = (codeMat 423 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 181 : Mat3).transpose * (codeMat 423 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s26_actual_le_transport :
    o451ActualSourceSpan ⟨26, by omega⟩ ≤ actionW (codeMat 95) (codeMat 181) step81o17s4Wspan := by
  apply o451_spanCodes_le_of_gens [257, 131, 67, 35, 19, 10, 5]
    (actionW (codeMat 95) (codeMat 181) step81o17s4Wspan)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 91 (by decide))
      (by unfold actionA; rw [o451d_s26_QtInv]; show (codeMat 95 : Mat3).transpose * codeMat 91 * (codeMat 423 : Mat3).transpose = codeMat 257; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 502 (by decide))
      (by unfold actionA; rw [o451d_s26_QtInv]; show (codeMat 95 : Mat3).transpose * codeMat 502 * (codeMat 423 : Mat3).transpose = codeMat 131; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 457 (by decide))
      (by unfold actionA; rw [o451d_s26_QtInv]; show (codeMat 95 : Mat3).transpose * codeMat 457 * (codeMat 423 : Mat3).transpose = codeMat 67; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 280 (by decide))
      (by unfold actionA; rw [o451d_s26_QtInv]; show (codeMat 95 : Mat3).transpose * codeMat 280 * (codeMat 423 : Mat3).transpose = codeMat 35; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 112 (by decide))
      (by unfold actionA; rw [o451d_s26_QtInv]; show (codeMat 95 : Mat3).transpose * codeMat 112 * (codeMat 423 : Mat3).transpose = codeMat 19; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 456 (by decide))
      (by unfold actionA; rw [o451d_s26_QtInv]; show (codeMat 95 : Mat3).transpose * codeMat 456 * (codeMat 423 : Mat3).transpose = codeMat 10; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h6
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 128 (by decide))
      (by unfold actionA; rw [o451d_s26_QtInv]; show (codeMat 95 : Mat3).transpose * codeMat 128 * (codeMat 423 : Mat3).transpose = codeMat 5; ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o451d_s26_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨26, by omega⟩) 14 :=
  quotientRankAtLeast_mono o451d_s26_actual_le_transport (o451_qra_action_code 95 181 (by decide) (by decide) step81o17s4Span_lb)

private theorem o451d_s26_qra : QuotientRankAtLeast (o451SourceU ⟨26, by omega⟩) 14 :=
  quotientRankAtLeast_mono o451s26_sourceU_le_actual o451d_s26_qra_actual

-- Source 27: orbit 17, lb=14, action, P=93, Q=254, Qinv=443
private theorem o451d_s27_QtInv :
    (codeMat 254 : Mat3).transpose⁻¹ = (codeMat 443 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 254 : Mat3).transpose * (codeMat 443 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s27_actual_le_transport :
    o451ActualSourceSpan ⟨27, by omega⟩ ≤ actionW (codeMat 93) (codeMat 254) step81o17s4Wspan := by
  apply o451_spanCodes_le_of_gens [257, 131, 64, 34, 19, 10, 7]
    (actionW (codeMat 93) (codeMat 254) step81o17s4Wspan)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 323 (by decide))
      (by unfold actionA; rw [o451d_s27_QtInv]; show (codeMat 93 : Mat3).transpose * codeMat 323 * (codeMat 443 : Mat3).transpose = codeMat 257; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 391 (by decide))
      (by unfold actionA; rw [o451d_s27_QtInv]; show (codeMat 93 : Mat3).transpose * codeMat 391 * (codeMat 443 : Mat3).transpose = codeMat 131; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 390 (by decide))
      (by unfold actionA; rw [o451d_s27_QtInv]; show (codeMat 93 : Mat3).transpose * codeMat 390 * (codeMat 443 : Mat3).transpose = codeMat 64; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 280 (by decide))
      (by unfold actionA; rw [o451d_s27_QtInv]; show (codeMat 93 : Mat3).transpose * codeMat 280 * (codeMat 443 : Mat3).transpose = codeMat 34; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 440 (by decide))
      (by unfold actionA; rw [o451d_s27_QtInv]; show (codeMat 93 : Mat3).transpose * codeMat 440 * (codeMat 443 : Mat3).transpose = codeMat 19; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 112 (by decide))
      (by unfold actionA; rw [o451d_s27_QtInv]; show (codeMat 93 : Mat3).transpose * codeMat 112 * (codeMat 443 : Mat3).transpose = codeMat 10; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h6
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 128 (by decide))
      (by unfold actionA; rw [o451d_s27_QtInv]; show (codeMat 93 : Mat3).transpose * codeMat 128 * (codeMat 443 : Mat3).transpose = codeMat 7; ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o451d_s27_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨27, by omega⟩) 14 :=
  quotientRankAtLeast_mono o451d_s27_actual_le_transport (o451_qra_action_code 93 254 (by decide) (by decide) step81o17s4Span_lb)

private theorem o451d_s27_qra : QuotientRankAtLeast (o451SourceU ⟨27, by omega⟩) 14 :=
  quotientRankAtLeast_mono o451s27_sourceU_le_actual o451d_s27_qra_actual

-- Source 28: orbit 10, lb=12, action, P=84, Q=212, Qinv=86
private theorem o451d_s28_QtInv :
    (codeMat 212 : Mat3).transpose⁻¹ = (codeMat 86 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 212 : Mat3).transpose * (codeMat 86 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s28_actual_le_transport :
    o451ActualSourceSpan ⟨28, by omega⟩ ≤ actionW (codeMat 84) (codeMat 212) orbit10W := by
  apply o451_spanCodes_le_of_gens [256, 132, 68, 32, 18, 10, 1]
    (actionW (codeMat 84) (codeMat 212) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide))
      (by unfold actionA; rw [o451d_s28_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 86 : Mat3).transpose = codeMat 256; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 70 (by decide))
      (by unfold actionA; rw [o451d_s28_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 70 * (codeMat 86 : Mat3).transpose = codeMat 132; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide))
      (by unfold actionA; rw [o451d_s28_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 68 * (codeMat 86 : Mat3).transpose = codeMat 68; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide))
      (by unfold actionA; rw [o451d_s28_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 86 : Mat3).transpose = codeMat 32; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 432 (by decide))
      (by unfold actionA; rw [o451d_s28_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 432 * (codeMat 86 : Mat3).transpose = codeMat 18; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 416 (by decide))
      (by unfold actionA; rw [o451d_s28_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 416 * (codeMat 86 : Mat3).transpose = codeMat 10; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h6
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide))
      (by unfold actionA; rw [o451d_s28_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 86 : Mat3).transpose = codeMat 1; ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o451d_s28_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨28, by omega⟩) 12 :=
  quotientRankAtLeast_mono o451d_s28_actual_le_transport (o451_qra_action_code 84 212 (by decide) (by decide) orbit10_lb12)

private theorem o451d_s28_qra : QuotientRankAtLeast (o451SourceU ⟨28, by omega⟩) 12 :=
  quotientRankAtLeast_mono o451s28_sourceU_le_actual o451d_s28_qra_actual

-- Source 29: orbit 10, lb=12, action, P=92, Q=84, Qinv=84
private theorem o451d_s29_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s29_actual_le_transport :
    o451ActualSourceSpan ⟨29, by omega⟩ ≤ actionW (codeMat 92) (codeMat 84) orbit10W := by
  apply o451_spanCodes_le_of_gens [256, 128, 68, 36, 18, 10, 1]
    (actionW (codeMat 92) (codeMat 84) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide))
      (by unfold actionA; rw [o451d_s29_QtInv]; show (codeMat 92 : Mat3).transpose * codeMat 1 * (codeMat 84 : Mat3).transpose = codeMat 256; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide))
      (by unfold actionA; rw [o451d_s29_QtInv]; show (codeMat 92 : Mat3).transpose * codeMat 2 * (codeMat 84 : Mat3).transpose = codeMat 128; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide))
      (by unfold actionA; rw [o451d_s29_QtInv]; show (codeMat 92 : Mat3).transpose * codeMat 68 * (codeMat 84 : Mat3).transpose = codeMat 68; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide))
      (by unfold actionA; rw [o451d_s29_QtInv]; show (codeMat 92 : Mat3).transpose * codeMat 8 * (codeMat 84 : Mat3).transpose = codeMat 36; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide))
      (by unfold actionA; rw [o451d_s29_QtInv]; show (codeMat 92 : Mat3).transpose * codeMat 16 * (codeMat 84 : Mat3).transpose = codeMat 18; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 416 (by decide))
      (by unfold actionA; rw [o451d_s29_QtInv]; show (codeMat 92 : Mat3).transpose * codeMat 416 * (codeMat 84 : Mat3).transpose = codeMat 10; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h6
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide))
      (by unfold actionA; rw [o451d_s29_QtInv]; show (codeMat 92 : Mat3).transpose * codeMat 256 * (codeMat 84 : Mat3).transpose = codeMat 1; ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o451d_s29_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨29, by omega⟩) 12 :=
  quotientRankAtLeast_mono o451d_s29_actual_le_transport (o451_qra_action_code 92 84 (by decide) (by decide) orbit10_lb12)

private theorem o451d_s29_qra : QuotientRankAtLeast (o451SourceU ⟨29, by omega⟩) 12 :=
  quotientRankAtLeast_mono o451s29_sourceU_le_actual o451d_s29_qra_actual

-- Source 30: orbit 10, lb=12, action, P=140, Q=156, Qinv=102
private theorem o451d_s30_QtInv :
    (codeMat 156 : Mat3).transpose⁻¹ = (codeMat 102 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 156 : Mat3).transpose * (codeMat 102 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s30_actual_le_transport :
    o451ActualSourceSpan ⟨30, by omega⟩ ≤ actionW (codeMat 140) (codeMat 156) orbit10W := by
  apply o451_spanCodes_le_of_gens [256, 160, 64, 18, 10, 4, 1]
    (actionW (codeMat 140) (codeMat 156) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide))
      (by unfold actionA; rw [o451d_s30_QtInv]; show (codeMat 140 : Mat3).transpose * codeMat 1 * (codeMat 102 : Mat3).transpose = codeMat 256; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 70 (by decide))
      (by unfold actionA; rw [o451d_s30_QtInv]; show (codeMat 140 : Mat3).transpose * codeMat 70 * (codeMat 102 : Mat3).transpose = codeMat 160; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide))
      (by unfold actionA; rw [o451d_s30_QtInv]; show (codeMat 140 : Mat3).transpose * codeMat 2 * (codeMat 102 : Mat3).transpose = codeMat 64; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 432 (by decide))
      (by unfold actionA; rw [o451d_s30_QtInv]; show (codeMat 140 : Mat3).transpose * codeMat 432 * (codeMat 102 : Mat3).transpose = codeMat 18; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 176 (by decide))
      (by unfold actionA; rw [o451d_s30_QtInv]; show (codeMat 140 : Mat3).transpose * codeMat 176 * (codeMat 102 : Mat3).transpose = codeMat 10; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide))
      (by unfold actionA; rw [o451d_s30_QtInv]; show (codeMat 140 : Mat3).transpose * codeMat 8 * (codeMat 102 : Mat3).transpose = codeMat 4; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h6
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide))
      (by unfold actionA; rw [o451d_s30_QtInv]; show (codeMat 140 : Mat3).transpose * codeMat 16 * (codeMat 102 : Mat3).transpose = codeMat 1; ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o451d_s30_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨30, by omega⟩) 12 :=
  quotientRankAtLeast_mono o451d_s30_actual_le_transport (o451_qra_action_code 140 156 (by decide) (by decide) orbit10_lb12)

private theorem o451d_s30_qra : QuotientRankAtLeast (o451SourceU ⟨30, by omega⟩) 12 :=
  quotientRankAtLeast_mono o451s30_sourceU_le_actual o451d_s30_qra_actual

-- Source 31: orbit 10, lb=12, action, P=266, Q=282, Qinv=267
private theorem o451d_s31_QtInv :
    (codeMat 282 : Mat3).transpose⁻¹ = (codeMat 267 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 282 : Mat3).transpose * (codeMat 267 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s31_actual_le_transport :
    o451ActualSourceSpan ⟨31, by omega⟩ ≤ actionW (codeMat 266) (codeMat 282) orbit10W := by
  apply o451_spanCodes_le_of_gens [256, 164, 68, 16, 8, 2, 1]
    (actionW (codeMat 266) (codeMat 282) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide))
      (by unfold actionA; rw [o451d_s31_QtInv]; show (codeMat 266 : Mat3).transpose * codeMat 256 * (codeMat 267 : Mat3).transpose = codeMat 256; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 228 (by decide))
      (by unfold actionA; rw [o451d_s31_QtInv]; show (codeMat 266 : Mat3).transpose * codeMat 228 * (codeMat 267 : Mat3).transpose = codeMat 164; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide))
      (by unfold actionA; rw [o451d_s31_QtInv]; show (codeMat 266 : Mat3).transpose * codeMat 160 * (codeMat 267 : Mat3).transpose = codeMat 68; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 3 (by decide))
      (by unfold actionA; rw [o451d_s31_QtInv]; show (codeMat 266 : Mat3).transpose * codeMat 3 * (codeMat 267 : Mat3).transpose = codeMat 16; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide))
      (by unfold actionA; rw [o451d_s31_QtInv]; show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 267 : Mat3).transpose = codeMat 8; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide))
      (by unfold actionA; rw [o451d_s31_QtInv]; show (codeMat 266 : Mat3).transpose * codeMat 24 * (codeMat 267 : Mat3).transpose = codeMat 2; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h6
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide))
      (by unfold actionA; rw [o451d_s31_QtInv]; show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 267 : Mat3).transpose = codeMat 1; ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o451d_s31_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨31, by omega⟩) 12 :=
  quotientRankAtLeast_mono o451d_s31_actual_le_transport (o451_qra_action_code 266 282 (by decide) (by decide) orbit10_lb12)

private theorem o451d_s31_qra : QuotientRankAtLeast (o451SourceU ⟨31, by omega⟩) 12 :=
  quotientRankAtLeast_mono o451s31_sourceU_le_actual o451d_s31_qra_actual

-- Source 32: orbit 3, lb=9, action, P=84, Q=369, Qinv=377
private theorem o451d_s32_QtInv :
    (codeMat 369 : Mat3).transpose⁻¹ = (codeMat 377 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 369 : Mat3).transpose * (codeMat 377 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s32_actual_le_transport :
    o451ActualSourceSpan ⟨32, by omega⟩ ≤ actionW (codeMat 84) (codeMat 369) flatW_3 := by
  apply o451_spanCodes_le_of_gens [257, 128, 65, 33, 17, 8, 4, 2]
    (actionW (codeMat 84) (codeMat 369) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 326 (by decide))
      (by unfold actionA; rw [o451d_s32_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 326 * (codeMat 377 : Mat3).transpose = codeMat 257; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 2 (by decide))
      (by unfold actionA; rw [o451d_s32_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 377 : Mat3).transpose = codeMat 128; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 325 (by decide))
      (by unfold actionA; rw [o451d_s32_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 325 * (codeMat 377 : Mat3).transpose = codeMat 65; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 368 (by decide))
      (by unfold actionA; rw [o451d_s32_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 368 * (codeMat 377 : Mat3).transpose = codeMat 33; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 336 (by decide))
      (by unfold actionA; rw [o451d_s32_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 336 * (codeMat 377 : Mat3).transpose = codeMat 17; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 40 (by decide))
      (by unfold actionA; rw [o451d_s32_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 40 * (codeMat 377 : Mat3).transpose = codeMat 8; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h6
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide))
      (by unfold actionA; rw [o451d_s32_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 377 : Mat3).transpose = codeMat 4; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h7
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide))
      (by unfold actionA; rw [o451d_s32_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 377 : Mat3).transpose = codeMat 2; ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o451d_s32_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨32, by omega⟩) 9 :=
  quotientRankAtLeast_mono o451d_s32_actual_le_transport (o451_qra_action_code 84 369 (by decide) (by decide) flatSeed_3)

private theorem o451d_s32_qra : QuotientRankAtLeast (o451SourceU ⟨32, by omega⟩) 9 :=
  quotientRankAtLeast_mono o451s32_sourceU_le_actual o451d_s32_qra_actual

-- Source 33: orbit 3, lb=9, action, P=84, Q=405, Qinv=407
private theorem o451d_s33_QtInv :
    (codeMat 405 : Mat3).transpose⁻¹ = (codeMat 407 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 405 : Mat3).transpose * (codeMat 407 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s33_actual_le_transport :
    o451ActualSourceSpan ⟨33, by omega⟩ ≤ actionW (codeMat 84) (codeMat 405) flatW_3 := by
  apply o451_spanCodes_le_of_gens [257, 129, 64, 32, 17, 8, 5, 2]
    (actionW (codeMat 84) (codeMat 405) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 69 (by decide))
      (by unfold actionA; rw [o451d_s33_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 69 * (codeMat 407 : Mat3).transpose = codeMat 257; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 70 (by decide))
      (by unfold actionA; rw [o451d_s33_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 70 * (codeMat 407 : Mat3).transpose = codeMat 129; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 1 (by decide))
      (by unfold actionA; rw [o451d_s33_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 407 : Mat3).transpose = codeMat 64; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 40 (by decide))
      (by unfold actionA; rw [o451d_s33_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 40 * (codeMat 407 : Mat3).transpose = codeMat 32; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 112 (by decide))
      (by unfold actionA; rw [o451d_s33_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 112 * (codeMat 407 : Mat3).transpose = codeMat 17; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 8 (by decide))
      (by unfold actionA; rw [o451d_s33_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 407 : Mat3).transpose = codeMat 8; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h6
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 256 (by decide))
      (by unfold actionA; rw [o451d_s33_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 407 : Mat3).transpose = codeMat 5; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h7
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide))
      (by unfold actionA; rw [o451d_s33_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 407 : Mat3).transpose = codeMat 2; ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o451d_s33_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨33, by omega⟩) 9 :=
  quotientRankAtLeast_mono o451d_s33_actual_le_transport (o451_qra_action_code 84 405 (by decide) (by decide) flatSeed_3)

private theorem o451d_s33_qra : QuotientRankAtLeast (o451SourceU ⟨33, by omega⟩) 9 :=
  quotientRankAtLeast_mono o451s33_sourceU_le_actual o451d_s33_qra_actual

-- Source 34: orbit 3, lb=9, action, P=84, Q=501, Qinv=494
private theorem o451d_s34_QtInv :
    (codeMat 501 : Mat3).transpose⁻¹ = (codeMat 494 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 501 : Mat3).transpose * (codeMat 494 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s34_actual_le_transport :
    o451ActualSourceSpan ⟨34, by omega⟩ ≤ actionW (codeMat 84) (codeMat 501) flatW_3 := by
  apply o451_spanCodes_le_of_gens [257, 129, 65, 33, 17, 8, 5, 2]
    (actionW (codeMat 84) (codeMat 501) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 327 (by decide))
      (by unfold actionA; rw [o451d_s34_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 327 * (codeMat 494 : Mat3).transpose = codeMat 257; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 326 (by decide))
      (by unfold actionA; rw [o451d_s34_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 326 * (codeMat 494 : Mat3).transpose = codeMat 129; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 325 (by decide))
      (by unfold actionA; rw [o451d_s34_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 325 * (codeMat 494 : Mat3).transpose = codeMat 65; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 376 (by decide))
      (by unfold actionA; rw [o451d_s34_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 376 * (codeMat 494 : Mat3).transpose = codeMat 33; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 368 (by decide))
      (by unfold actionA; rw [o451d_s34_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 368 * (codeMat 494 : Mat3).transpose = codeMat 17; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 40 (by decide))
      (by unfold actionA; rw [o451d_s34_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 40 * (codeMat 494 : Mat3).transpose = codeMat 8; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h6
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide))
      (by unfold actionA; rw [o451d_s34_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 494 : Mat3).transpose = codeMat 5; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h7
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide))
      (by unfold actionA; rw [o451d_s34_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 494 : Mat3).transpose = codeMat 2; ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o451d_s34_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨34, by omega⟩) 9 :=
  quotientRankAtLeast_mono o451d_s34_actual_le_transport (o451_qra_action_code 84 501 (by decide) (by decide) flatSeed_3)

private theorem o451d_s34_qra : QuotientRankAtLeast (o451SourceU ⟨34, by omega⟩) 9 :=
  quotientRankAtLeast_mono o451s34_sourceU_le_actual o451d_s34_qra_actual

-- Source 35: orbit 3, lb=9, action, P=84, Q=491, Qinv=375
private theorem o451d_s35_QtInv :
    (codeMat 491 : Mat3).transpose⁻¹ = (codeMat 375 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 491 : Mat3).transpose * (codeMat 375 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s35_actual_le_transport :
    o451ActualSourceSpan ⟨35, by omega⟩ ≤ actionW (codeMat 84) (codeMat 491) flatW_3 := by
  apply o451_spanCodes_le_of_gens [257, 129, 65, 33, 16, 9, 4, 3]
    (actionW (codeMat 84) (codeMat 491) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 454 (by decide))
      (by unfold actionA; rw [o451d_s35_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 454 * (codeMat 375 : Mat3).transpose = codeMat 257; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 453 (by decide))
      (by unfold actionA; rw [o451d_s35_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 453 * (codeMat 375 : Mat3).transpose = codeMat 129; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 455 (by decide))
      (by unfold actionA; rw [o451d_s35_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 455 * (codeMat 375 : Mat3).transpose = codeMat 65; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 496 (by decide))
      (by unfold actionA; rw [o451d_s35_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 496 * (codeMat 375 : Mat3).transpose = codeMat 33; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 40 (by decide))
      (by unfold actionA; rw [o451d_s35_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 40 * (codeMat 375 : Mat3).transpose = codeMat 16; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 504 (by decide))
      (by unfold actionA; rw [o451d_s35_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 504 * (codeMat 375 : Mat3).transpose = codeMat 9; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h6
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide))
      (by unfold actionA; rw [o451d_s35_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 375 : Mat3).transpose = codeMat 4; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h7
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide))
      (by unfold actionA; rw [o451d_s35_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 375 : Mat3).transpose = codeMat 3; ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o451d_s35_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨35, by omega⟩) 9 :=
  quotientRankAtLeast_mono o451d_s35_actual_le_transport (o451_qra_action_code 84 491 (by decide) (by decide) flatSeed_3)

private theorem o451d_s35_qra : QuotientRankAtLeast (o451SourceU ⟨35, by omega⟩) 9 :=
  quotientRankAtLeast_mono o451s35_sourceU_le_actual o451d_s35_qra_actual

-- Source 36: orbit 3, lb=9, action, P=84, Q=335, Qinv=426
private theorem o451d_s36_QtInv :
    (codeMat 335 : Mat3).transpose⁻¹ = (codeMat 426 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 335 : Mat3).transpose * (codeMat 426 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s36_actual_le_transport :
    o451ActualSourceSpan ⟨36, by omega⟩ ≤ actionW (codeMat 84) (codeMat 335) flatW_3 := by
  apply o451_spanCodes_le_of_gens [257, 128, 65, 32, 16, 9, 5, 3]
    (actionW (codeMat 84) (codeMat 335) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 453 (by decide))
      (by unfold actionA; rw [o451d_s36_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 453 * (codeMat 426 : Mat3).transpose = codeMat 257; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 1 (by decide))
      (by unfold actionA; rw [o451d_s36_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 426 : Mat3).transpose = codeMat 128; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 455 (by decide))
      (by unfold actionA; rw [o451d_s36_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 455 * (codeMat 426 : Mat3).transpose = codeMat 65; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 40 (by decide))
      (by unfold actionA; rw [o451d_s36_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 40 * (codeMat 426 : Mat3).transpose = codeMat 32; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 8 (by decide))
      (by unfold actionA; rw [o451d_s36_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 426 : Mat3).transpose = codeMat 16; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 504 (by decide))
      (by unfold actionA; rw [o451d_s36_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 504 * (codeMat 426 : Mat3).transpose = codeMat 9; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h6
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide))
      (by unfold actionA; rw [o451d_s36_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 426 : Mat3).transpose = codeMat 5; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h7
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide))
      (by unfold actionA; rw [o451d_s36_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 426 : Mat3).transpose = codeMat 3; ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o451d_s36_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨36, by omega⟩) 9 :=
  quotientRankAtLeast_mono o451d_s36_actual_le_transport (o451_qra_action_code 84 335 (by decide) (by decide) flatSeed_3)

private theorem o451d_s36_qra : QuotientRankAtLeast (o451SourceU ⟨36, by omega⟩) 9 :=
  quotientRankAtLeast_mono o451s36_sourceU_le_actual o451d_s36_qra_actual

-- Source 37: orbit 3, lb=9, action, P=84, Q=431, Qinv=477
private theorem o451d_s37_QtInv :
    (codeMat 431 : Mat3).transpose⁻¹ = (codeMat 477 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 431 : Mat3).transpose * (codeMat 477 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s37_actual_le_transport :
    o451ActualSourceSpan ⟨37, by omega⟩ ≤ actionW (codeMat 84) (codeMat 431) flatW_3 := by
  apply o451_spanCodes_le_of_gens [257, 129, 64, 33, 16, 9, 5, 3]
    (actionW (codeMat 84) (codeMat 431) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 199 (by decide))
      (by unfold actionA; rw [o451d_s37_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 199 * (codeMat 477 : Mat3).transpose = codeMat 257; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 197 (by decide))
      (by unfold actionA; rw [o451d_s37_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 197 * (codeMat 477 : Mat3).transpose = codeMat 129; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 3 (by decide))
      (by unfold actionA; rw [o451d_s37_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 3 * (codeMat 477 : Mat3).transpose = codeMat 64; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 248 (by decide))
      (by unfold actionA; rw [o451d_s37_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 248 * (codeMat 477 : Mat3).transpose = codeMat 33; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 40 (by decide))
      (by unfold actionA; rw [o451d_s37_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 40 * (codeMat 477 : Mat3).transpose = codeMat 16; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 216 (by decide))
      (by unfold actionA; rw [o451d_s37_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 216 * (codeMat 477 : Mat3).transpose = codeMat 9; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h6
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 256 (by decide))
      (by unfold actionA; rw [o451d_s37_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 477 : Mat3).transpose = codeMat 5; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h7
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide))
      (by unfold actionA; rw [o451d_s37_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 477 : Mat3).transpose = codeMat 3; ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o451d_s37_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨37, by omega⟩) 9 :=
  quotientRankAtLeast_mono o451d_s37_actual_le_transport (o451_qra_action_code 84 431 (by decide) (by decide) flatSeed_3)

private theorem o451d_s37_qra : QuotientRankAtLeast (o451SourceU ⟨37, by omega⟩) 9 :=
  quotientRankAtLeast_mono o451s37_sourceU_le_actual o451d_s37_qra_actual

-- Source 38: orbit 3, lb=9, action, P=84, Q=122, Qinv=460
private theorem o451d_s38_QtInv :
    (codeMat 122 : Mat3).transpose⁻¹ = (codeMat 460 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 122 : Mat3).transpose * (codeMat 460 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s38_actual_le_transport :
    o451ActualSourceSpan ⟨38, by omega⟩ ≤ actionW (codeMat 84) (codeMat 122) flatW_3 := by
  apply o451_spanCodes_le_of_gens [256, 128, 66, 34, 18, 10, 4, 1]
    (actionW (codeMat 84) (codeMat 122) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 2 (by decide))
      (by unfold actionA; rw [o451d_s38_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 460 : Mat3).transpose = codeMat 256; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 3 (by decide))
      (by unfold actionA; rw [o451d_s38_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 3 * (codeMat 460 : Mat3).transpose = codeMat 128; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 198 (by decide))
      (by unfold actionA; rw [o451d_s38_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 198 * (codeMat 460 : Mat3).transpose = codeMat 66; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 208 (by decide))
      (by unfold actionA; rw [o451d_s38_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 208 * (codeMat 460 : Mat3).transpose = codeMat 34; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 216 (by decide))
      (by unfold actionA; rw [o451d_s38_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 216 * (codeMat 460 : Mat3).transpose = codeMat 18; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 240 (by decide))
      (by unfold actionA; rw [o451d_s38_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 240 * (codeMat 460 : Mat3).transpose = codeMat 10; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h6
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide))
      (by unfold actionA; rw [o451d_s38_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 460 : Mat3).transpose = codeMat 4; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h7
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide))
      (by unfold actionA; rw [o451d_s38_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 460 : Mat3).transpose = codeMat 1; ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o451d_s38_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨38, by omega⟩) 9 :=
  quotientRankAtLeast_mono o451d_s38_actual_le_transport (o451_qra_action_code 84 122 (by decide) (by decide) flatSeed_3)

private theorem o451d_s38_qra : QuotientRankAtLeast (o451SourceU ⟨38, by omega⟩) 9 :=
  quotientRankAtLeast_mono o451s38_sourceU_le_actual o451d_s38_qra_actual

-- Source 39: orbit 3, lb=9, action, P=84, Q=250, Qinv=397
private theorem o451d_s39_QtInv :
    (codeMat 250 : Mat3).transpose⁻¹ = (codeMat 397 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 250 : Mat3).transpose * (codeMat 397 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s39_actual_le_transport :
    o451ActualSourceSpan ⟨39, by omega⟩ ≤ actionW (codeMat 84) (codeMat 250) flatW_3 := by
  apply o451_spanCodes_le_of_gens [256, 130, 66, 34, 18, 10, 4, 1]
    (actionW (codeMat 84) (codeMat 250) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 2 (by decide))
      (by unfold actionA; rw [o451d_s39_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 397 : Mat3).transpose = codeMat 256; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 455 (by decide))
      (by unfold actionA; rw [o451d_s39_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 455 * (codeMat 397 : Mat3).transpose = codeMat 130; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 454 (by decide))
      (by unfold actionA; rw [o451d_s39_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 454 * (codeMat 397 : Mat3).transpose = codeMat 66; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 464 (by decide))
      (by unfold actionA; rw [o451d_s39_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 464 * (codeMat 397 : Mat3).transpose = codeMat 34; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 504 (by decide))
      (by unfold actionA; rw [o451d_s39_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 504 * (codeMat 397 : Mat3).transpose = codeMat 18; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 496 (by decide))
      (by unfold actionA; rw [o451d_s39_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 496 * (codeMat 397 : Mat3).transpose = codeMat 10; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h6
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide))
      (by unfold actionA; rw [o451d_s39_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 397 : Mat3).transpose = codeMat 4; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h7
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide))
      (by unfold actionA; rw [o451d_s39_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 397 : Mat3).transpose = codeMat 1; ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o451d_s39_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨39, by omega⟩) 9 :=
  quotientRankAtLeast_mono o451d_s39_actual_le_transport (o451_qra_action_code 84 250 (by decide) (by decide) flatSeed_3)

private theorem o451d_s39_qra : QuotientRankAtLeast (o451SourceU ⟨39, by omega⟩) 9 :=
  quotientRankAtLeast_mono o451s39_sourceU_le_actual o451d_s39_qra_actual

-- Source 40: orbit 3, lb=9, action, P=84, Q=158, Qinv=358
private theorem o451d_s40_QtInv :
    (codeMat 158 : Mat3).transpose⁻¹ = (codeMat 358 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 158 : Mat3).transpose * (codeMat 358 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s40_actual_le_transport :
    o451ActualSourceSpan ⟨40, by omega⟩ ≤ actionW (codeMat 84) (codeMat 158) flatW_3 := by
  apply o451_spanCodes_le_of_gens [256, 130, 64, 32, 18, 10, 6, 1]
    (actionW (codeMat 84) (codeMat 158) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 1 (by decide))
      (by unfold actionA; rw [o451d_s40_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 358 : Mat3).transpose = codeMat 256; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 455 (by decide))
      (by unfold actionA; rw [o451d_s40_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 455 * (codeMat 358 : Mat3).transpose = codeMat 130; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 2 (by decide))
      (by unfold actionA; rw [o451d_s40_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 358 : Mat3).transpose = codeMat 64; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 8 (by decide))
      (by unfold actionA; rw [o451d_s40_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 358 : Mat3).transpose = codeMat 32; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 504 (by decide))
      (by unfold actionA; rw [o451d_s40_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 504 * (codeMat 358 : Mat3).transpose = codeMat 18; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 464 (by decide))
      (by unfold actionA; rw [o451d_s40_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 464 * (codeMat 358 : Mat3).transpose = codeMat 10; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h6
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide))
      (by unfold actionA; rw [o451d_s40_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 358 : Mat3).transpose = codeMat 6; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h7
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide))
      (by unfold actionA; rw [o451d_s40_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 358 : Mat3).transpose = codeMat 1; ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o451d_s40_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨40, by omega⟩) 9 :=
  quotientRankAtLeast_mono o451d_s40_actual_le_transport (o451_qra_action_code 84 158 (by decide) (by decide) flatSeed_3)

private theorem o451d_s40_qra : QuotientRankAtLeast (o451SourceU ⟨40, by omega⟩) 9 :=
  quotientRankAtLeast_mono o451s40_sourceU_le_actual o451d_s40_qra_actual

-- Source 41: orbit 3, lb=9, action, P=84, Q=94, Qinv=500
private theorem o451d_s41_QtInv :
    (codeMat 94 : Mat3).transpose⁻¹ = (codeMat 500 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 94 : Mat3).transpose * (codeMat 500 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s41_actual_le_transport :
    o451ActualSourceSpan ⟨41, by omega⟩ ≤ actionW (codeMat 84) (codeMat 94) flatW_3 := by
  apply o451_spanCodes_le_of_gens [256, 128, 66, 32, 18, 10, 6, 1]
    (actionW (codeMat 84) (codeMat 94) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 1 (by decide))
      (by unfold actionA; rw [o451d_s41_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 500 : Mat3).transpose = codeMat 256; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 3 (by decide))
      (by unfold actionA; rw [o451d_s41_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 3 * (codeMat 500 : Mat3).transpose = codeMat 128; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 198 (by decide))
      (by unfold actionA; rw [o451d_s41_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 198 * (codeMat 500 : Mat3).transpose = codeMat 66; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 8 (by decide))
      (by unfold actionA; rw [o451d_s41_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 500 : Mat3).transpose = codeMat 32; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 216 (by decide))
      (by unfold actionA; rw [o451d_s41_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 216 * (codeMat 500 : Mat3).transpose = codeMat 18; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 240 (by decide))
      (by unfold actionA; rw [o451d_s41_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 240 * (codeMat 500 : Mat3).transpose = codeMat 10; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h6
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide))
      (by unfold actionA; rw [o451d_s41_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 500 : Mat3).transpose = codeMat 6; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h7
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide))
      (by unfold actionA; rw [o451d_s41_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 500 : Mat3).transpose = codeMat 1; ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o451d_s41_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨41, by omega⟩) 9 :=
  quotientRankAtLeast_mono o451d_s41_actual_le_transport (o451_qra_action_code 84 94 (by decide) (by decide) flatSeed_3)

private theorem o451d_s41_qra : QuotientRankAtLeast (o451SourceU ⟨41, by omega⟩) 9 :=
  quotientRankAtLeast_mono o451s41_sourceU_le_actual o451d_s41_qra_actual

-- Source 42: orbit 3, lb=9, action, P=84, Q=190, Qinv=355
private theorem o451d_s42_QtInv :
    (codeMat 190 : Mat3).transpose⁻¹ = (codeMat 355 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 190 : Mat3).transpose * (codeMat 355 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s42_actual_le_transport :
    o451ActualSourceSpan ⟨42, by omega⟩ ≤ actionW (codeMat 84) (codeMat 190) flatW_3 := by
  apply o451_spanCodes_le_of_gens [256, 130, 64, 34, 18, 10, 6, 1]
    (actionW (codeMat 84) (codeMat 190) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 3 (by decide))
      (by unfold actionA; rw [o451d_s42_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 3 * (codeMat 355 : Mat3).transpose = codeMat 256; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 455 (by decide))
      (by unfold actionA; rw [o451d_s42_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 455 * (codeMat 355 : Mat3).transpose = codeMat 130; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 2 (by decide))
      (by unfold actionA; rw [o451d_s42_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 355 : Mat3).transpose = codeMat 64; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 472 (by decide))
      (by unfold actionA; rw [o451d_s42_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 472 * (codeMat 355 : Mat3).transpose = codeMat 34; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 504 (by decide))
      (by unfold actionA; rw [o451d_s42_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 504 * (codeMat 355 : Mat3).transpose = codeMat 18; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 464 (by decide))
      (by unfold actionA; rw [o451d_s42_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 464 * (codeMat 355 : Mat3).transpose = codeMat 10; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h6
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 256 (by decide))
      (by unfold actionA; rw [o451d_s42_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 355 : Mat3).transpose = codeMat 6; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h7
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide))
      (by unfold actionA; rw [o451d_s42_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 355 : Mat3).transpose = codeMat 1; ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o451d_s42_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨42, by omega⟩) 9 :=
  quotientRankAtLeast_mono o451d_s42_actual_le_transport (o451_qra_action_code 84 190 (by decide) (by decide) flatSeed_3)

private theorem o451d_s42_qra : QuotientRankAtLeast (o451SourceU ⟨42, by omega⟩) 9 :=
  quotientRankAtLeast_mono o451s42_sourceU_le_actual o451d_s42_qra_actual

-- Source 43: orbit 3, lb=9, action, P=84, Q=254, Qinv=443
private theorem o451d_s43_QtInv :
    (codeMat 254 : Mat3).transpose⁻¹ = (codeMat 443 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 254 : Mat3).transpose * (codeMat 443 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o451d_s43_actual_le_transport :
    o451ActualSourceSpan ⟨43, by omega⟩ ≤ actionW (codeMat 84) (codeMat 254) flatW_3 := by
  apply o451_spanCodes_le_of_gens [256, 130, 66, 34, 18, 10, 6, 1]
    (actionW (codeMat 84) (codeMat 254) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 3 (by decide))
      (by unfold actionA; rw [o451d_s43_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 3 * (codeMat 443 : Mat3).transpose = codeMat 256; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 455 (by decide))
      (by unfold actionA; rw [o451d_s43_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 455 * (codeMat 443 : Mat3).transpose = codeMat 130; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 454 (by decide))
      (by unfold actionA; rw [o451d_s43_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 454 * (codeMat 443 : Mat3).transpose = codeMat 66; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 472 (by decide))
      (by unfold actionA; rw [o451d_s43_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 472 * (codeMat 443 : Mat3).transpose = codeMat 34; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 504 (by decide))
      (by unfold actionA; rw [o451d_s43_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 504 * (codeMat 443 : Mat3).transpose = codeMat 18; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 496 (by decide))
      (by unfold actionA; rw [o451d_s43_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 496 * (codeMat 443 : Mat3).transpose = codeMat 10; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h6
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 256 (by decide))
      (by unfold actionA; rw [o451d_s43_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 443 : Mat3).transpose = codeMat 6; ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h7
    exact o451_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide))
      (by unfold actionA; rw [o451d_s43_QtInv]; show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 443 : Mat3).transpose = codeMat 1; ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o451d_s43_qra_actual : QuotientRankAtLeast (o451ActualSourceSpan ⟨43, by omega⟩) 9 :=
  quotientRankAtLeast_mono o451d_s43_actual_le_transport (o451_qra_action_code 84 254 (by decide) (by decide) flatSeed_3)

private theorem o451d_s43_qra : QuotientRankAtLeast (o451SourceU ⟨43, by omega⟩) 9 :=
  quotientRankAtLeast_mono o451s43_sourceU_le_actual o451d_s43_qra_actual

private theorem o451_dispatch_hSource (i : Fin 44) :
    QuotientRankAtLeast (o451SourceU i) (o451SourceLb i) := by
  fin_cases i <;> simp only [o451SourceLb]
  · exact o451d_s0_qra
  · exact o451d_s1_qra
  · exact o451d_s2_qra
  · exact o451d_s3_qra
  · exact o451d_s4_qra
  · exact o451d_s5_qra
  · exact o451d_s6_qra
  · exact o451d_s7_qra
  · exact o451d_s8_qra
  · exact o451d_s9_qra
  · exact o451d_s10_qra
  · exact o451d_s11_qra
  · exact o451d_s12_qra
  · exact o451d_s13_qra
  · exact o451d_s14_qra
  · exact o451d_s15_qra
  · exact o451d_s16_qra
  · exact o451d_s17_qra
  · exact o451d_s18_qra
  · exact o451d_s19_qra
  · exact o451d_s20_qra
  · exact o451d_s21_qra
  · exact o451d_s22_qra
  · exact o451d_s23_qra
  · exact o451d_s24_qra
  · exact o451d_s25_qra
  · exact o451d_s26_qra
  · exact o451d_s27_qra
  · exact o451d_s28_qra
  · exact o451d_s29_qra
  · exact o451d_s30_qra
  · exact o451d_s31_qra
  · exact o451d_s32_qra
  · exact o451d_s33_qra
  · exact o451d_s34_qra
  · exact o451d_s35_qra
  · exact o451d_s36_qra
  · exact o451d_s37_qra
  · exact o451d_s38_qra
  · exact o451d_s39_qra
  · exact o451d_s40_qra
  · exact o451d_s41_qra
  · exact o451d_s42_qra
  · exact o451d_s43_qra

theorem step126_orbit451_lb18 : QuotientRankAtLeast o451W 18 :=
  o451ScalarLb18 o451_dispatch_hSource

end QiushiMatmul
end
