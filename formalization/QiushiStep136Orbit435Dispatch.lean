import QiushiStep136Orbit435Core
import QiushiStep136Orbit435Bridges
import QiushiCodeSpanCore
import QiushiMonoOrbit342From196
import QiushiMonoOrbit95From31
import QiushiOrbit10FP
import QiushiOrbit31FP
import QiushiStep128Mono158From72
import QiushiStep81Qdim2Generated
import QiushiStep99Orbit144Dispatch
import QiushiStep99Orbit196Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit72Dispatch
import QiushiTransposeTransport
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiFlattenSeeds

set_option maxHeartbeats 800000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
open BigOperators Finset Matrix Classical
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem o435_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by intro M hM; rcases hM with ⟨n, hn, rfl⟩; exact h n hn)

private theorem o435_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  exact ⟨codeMat witness, h_mem, h_action⟩

private theorem o435_qra_action_code (Pcode Qcode : Nat)
    {W : Submodule F2 Mat3} {n : ℕ}
    (hPdet : IsUnit (codeMat Pcode : Mat3).det)
    (hQdet : IsUnit (codeMat Qcode : Mat3).det)
    (h : QuotientRankAtLeast W n) :
    QuotientRankAtLeast (actionW (codeMat Pcode) (codeMat Qcode) W) n := by
  have hP : Invertible (codeMat Pcode : Mat3) := Matrix.invertibleOfIsUnitDet _ hPdet
  have hQ : Invertible (codeMat Qcode : Mat3) := Matrix.invertibleOfIsUnitDet _ hQdet
  exact @quotientRankAtLeast_action (codeMat Pcode) (codeMat Qcode) hP hQ W n h

private theorem o435_QtInv_481_185 :
    (codeMat 481 : Mat3).transpose⁻¹ = (codeMat 185 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 481 : Mat3).transpose * (codeMat 185 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o435_QtInv_250_397 :
    (codeMat 250 : Mat3).transpose⁻¹ = (codeMat 397 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 250 : Mat3).transpose * (codeMat 397 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o435_QtInv_92_116 :
    (codeMat 92 : Mat3).transpose⁻¹ = (codeMat 116 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 92 : Mat3).transpose * (codeMat 116 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o435_QtInv_477_431 :
    (codeMat 477 : Mat3).transpose⁻¹ = (codeMat 431 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 477 : Mat3).transpose * (codeMat 431 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o435_QtInv_474_395 :
    (codeMat 474 : Mat3).transpose⁻¹ = (codeMat 395 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 474 : Mat3).transpose * (codeMat 395 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o435_QtInv_188_103 :
    (codeMat 188 : Mat3).transpose⁻¹ = (codeMat 103 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 188 : Mat3).transpose * (codeMat 103 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o435_QtInv_254_443 :
    (codeMat 254 : Mat3).transpose⁻¹ = (codeMat 443 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 254 : Mat3).transpose * (codeMat 443 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o435_QtInv_412_111 :
    (codeMat 412 : Mat3).transpose⁻¹ = (codeMat 111 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 412 : Mat3).transpose * (codeMat 111 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o435_QtInv_444_110 :
    (codeMat 444 : Mat3).transpose⁻¹ = (codeMat 110 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 444 : Mat3).transpose * (codeMat 110 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o435_QtInv_478_445 :
    (codeMat 478 : Mat3).transpose⁻¹ = (codeMat 445 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 478 : Mat3).transpose * (codeMat 445 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o435_QtInv_253_415 :
    (codeMat 253 : Mat3).transpose⁻¹ = (codeMat 415 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 253 : Mat3).transpose * (codeMat 415 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o435_QtInv_156_102 :
    (codeMat 156 : Mat3).transpose⁻¹ = (codeMat 102 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 156 : Mat3).transpose * (codeMat 102 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o435_QtInv_249_425 :
    (codeMat 249 : Mat3).transpose⁻¹ = (codeMat 425 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 249 : Mat3).transpose * (codeMat 425 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o435_QtInv_394_330 :
    (codeMat 394 : Mat3).transpose⁻¹ = (codeMat 330 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 394 : Mat3).transpose * (codeMat 330 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o435_QtInv_122_460 :
    (codeMat 122 : Mat3).transpose⁻¹ = (codeMat 460 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 122 : Mat3).transpose * (codeMat 460 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o435_QtInv_498_206 :
    (codeMat 498 : Mat3).transpose⁻¹ = (codeMat 206 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 498 : Mat3).transpose * (codeMat 206 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o435_QtInv_465_465 :
    (codeMat 465 : Mat3).transpose⁻¹ = (codeMat 465 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 465 : Mat3).transpose * (codeMat 465 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o435_QtInv_458_458 :
    (codeMat 458 : Mat3).transpose⁻¹ = (codeMat 458 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 458 : Mat3).transpose * (codeMat 458 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o435_QtInv_206_498 :
    (codeMat 206 : Mat3).transpose⁻¹ = (codeMat 498 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 206 : Mat3).transpose * (codeMat 498 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o435_QtInv_494_501 :
    (codeMat 494 : Mat3).transpose⁻¹ = (codeMat 501 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 494 : Mat3).transpose * (codeMat 501 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o435_QtInv_234_461 :
    (codeMat 234 : Mat3).transpose⁻¹ = (codeMat 461 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 234 : Mat3).transpose * (codeMat 461 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o435_QtInv_501_494 :
    (codeMat 501 : Mat3).transpose⁻¹ = (codeMat 494 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 501 : Mat3).transpose * (codeMat 494 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o435_QtInv_473_409 :
    (codeMat 473 : Mat3).transpose⁻¹ = (codeMat 409 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 473 : Mat3).transpose * (codeMat 409 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o435_QtInv_169_225 :
    (codeMat 169 : Mat3).transpose⁻¹ = (codeMat 225 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 169 : Mat3).transpose * (codeMat 225 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o435_QtInv_345_345 :
    (codeMat 345 : Mat3).transpose⁻¹ = (codeMat 345 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 345 : Mat3).transpose * (codeMat 345 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o435_QtInv_212_86 :
    (codeMat 212 : Mat3).transpose⁻¹ = (codeMat 86 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 212 : Mat3).transpose * (codeMat 86 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o435_QtInv_409_473 :
    (codeMat 409 : Mat3).transpose⁻¹ = (codeMat 473 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 409 : Mat3).transpose * (codeMat 473 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o435_QtInv_346_459 :
    (codeMat 346 : Mat3).transpose⁻¹ = (codeMat 459 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 346 : Mat3).transpose * (codeMat 459 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o435_QtInv_382_499 :
    (codeMat 382 : Mat3).transpose⁻¹ = (codeMat 499 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 382 : Mat3).transpose * (codeMat 499 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o435_QtInv_185_481 :
    (codeMat 185 : Mat3).transpose⁻¹ = (codeMat 481 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 185 : Mat3).transpose * (codeMat 481 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o435_QtInv_445_478 :
    (codeMat 445 : Mat3).transpose⁻¹ = (codeMat 478 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 445 : Mat3).transpose * (codeMat 478 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o435_QtInv_94_500 :
    (codeMat 94 : Mat3).transpose⁻¹ = (codeMat 500 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 94 : Mat3).transpose * (codeMat 500 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o435_QtInv_236_123 :
    (codeMat 236 : Mat3).transpose⁻¹ = (codeMat 123 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 236 : Mat3).transpose * (codeMat 123 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o435_QtInv_492_115 :
    (codeMat 492 : Mat3).transpose⁻¹ = (codeMat 115 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 492 : Mat3).transpose * (codeMat 115 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o435_QtInv_460_122 :
    (codeMat 460 : Mat3).transpose⁻¹ = (codeMat 122 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 460 : Mat3).transpose * (codeMat 122 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o435_QtInv_244_95 :
    (codeMat 244 : Mat3).transpose⁻¹ = (codeMat 95 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 244 : Mat3).transpose * (codeMat 95 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o435_QtInv_468_87 :
    (codeMat 468 : Mat3).transpose⁻¹ = (codeMat 87 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 468 : Mat3).transpose * (codeMat 87 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

-- Source 0: orbit342, lb=16, action, P=302, Q=481
private theorem o435d_s0_actual_le_transport :
    o435ActualSourceSpan ⟨0, by omega⟩ ≤
    actionW (codeMat 302) (codeMat 481) o342W_mono := by
  apply o435_spanCodes_le_of_gens [327, 193, 19, 10]
    (actionW (codeMat 302) (codeMat 481) o342W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [296, 100, 16, 1] 312 (by decide))
      (by unfold actionA; rw [o435_QtInv_481_185]
          show (codeMat 302 : Mat3).transpose * codeMat 312 * (codeMat 185 : Mat3).transpose = codeMat 327
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [296, 100, 16, 1] 296 (by decide))
      (by unfold actionA; rw [o435_QtInv_481_185]
          show (codeMat 302 : Mat3).transpose * codeMat 296 * (codeMat 185 : Mat3).transpose = codeMat 193
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [296, 100, 16, 1] 332 (by decide))
      (by unfold actionA; rw [o435_QtInv_481_185]
          show (codeMat 302 : Mat3).transpose * codeMat 332 * (codeMat 185 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [296, 100, 16, 1] 101 (by decide))
      (by unfold actionA; rw [o435_QtInv_481_185]
          show (codeMat 302 : Mat3).transpose * codeMat 101 * (codeMat 185 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s0_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨0, by omega⟩) 16 :=
  quotientRankAtLeast_mono o435d_s0_actual_le_transport
    (o435_qra_action_code 302 481 (by decide) (by decide) orbit342_lb16_mono)

private theorem o435d_s0_qra : QuotientRankAtLeast (o435SourceU ⟨0, by omega⟩) 16 :=
  quotientRankAtLeast_mono o435s0_sourceU_le_actual o435d_s0_qra_actual

-- Source 1: orbit144, lb=15, action, P=358, Q=250
private theorem o435d_s1_actual_le_transport :
    o435ActualSourceSpan ⟨1, by omega⟩ ≤
    actionW (codeMat 358) (codeMat 250) o144W := by
  apply o435_spanCodes_le_of_gens [288, 161, 96, 19, 10]
    (actionW (codeMat 358) (codeMat 250) o144W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 2 (by decide))
      (by unfold actionA; rw [o435_QtInv_250_397]
          show (codeMat 358 : Mat3).transpose * codeMat 2 * (codeMat 397 : Mat3).transpose = codeMat 288
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 410 (by decide))
      (by unfold actionA; rw [o435_QtInv_250_397]
          show (codeMat 358 : Mat3).transpose * codeMat 410 * (codeMat 397 : Mat3).transpose = codeMat 161
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 34 (by decide))
      (by unfold actionA; rw [o435_QtInv_250_397]
          show (codeMat 358 : Mat3).transpose * codeMat 34 * (codeMat 397 : Mat3).transpose = codeMat 96
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 119 (by decide))
      (by unfold actionA; rw [o435_QtInv_250_397]
          show (codeMat 358 : Mat3).transpose * codeMat 119 * (codeMat 397 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 462 (by decide))
      (by unfold actionA; rw [o435_QtInv_250_397]
          show (codeMat 358 : Mat3).transpose * codeMat 462 * (codeMat 397 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s1_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨1, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s1_actual_le_transport
    (o435_qra_action_code 358 250 (by decide) (by decide) step99_orbit144_lb15_unconditional)

private theorem o435d_s1_qra : QuotientRankAtLeast (o435SourceU ⟨1, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s1_sourceU_le_actual o435d_s1_qra_actual

-- Source 2: orbit196, lb=16, action, P=183, Q=92
private theorem o435d_s2_actual_le_transport :
    o435ActualSourceSpan ⟨2, by omega⟩ ≤
    actionW (codeMat 183) (codeMat 92) o196W := by
  apply o435_spanCodes_le_of_gens [292, 133, 68, 19, 10]
    (actionW (codeMat 183) (codeMat 92) o196W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 1 (by decide))
      (by unfold actionA; rw [o435_QtInv_92_116]
          show (codeMat 183 : Mat3).transpose * codeMat 1 * (codeMat 116 : Mat3).transpose = codeMat 292
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 175 (by decide))
      (by unfold actionA; rw [o435_QtInv_92_116]
          show (codeMat 183 : Mat3).transpose * codeMat 175 * (codeMat 116 : Mat3).transpose = codeMat 133
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 441 (by decide))
      (by unfold actionA; rw [o435_QtInv_92_116]
          show (codeMat 183 : Mat3).transpose * codeMat 441 * (codeMat 116 : Mat3).transpose = codeMat 68
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 164 (by decide))
      (by unfold actionA; rw [o435_QtInv_92_116]
          show (codeMat 183 : Mat3).transpose * codeMat 164 * (codeMat 116 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 402 (by decide))
      (by unfold actionA; rw [o435_QtInv_92_116]
          show (codeMat 183 : Mat3).transpose * codeMat 402 * (codeMat 116 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s2_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨2, by omega⟩) 16 :=
  quotientRankAtLeast_mono o435d_s2_actual_le_transport
    (o435_qra_action_code 183 92 (by decide) (by decide) step99_orbit196_lb16_unconditional)

private theorem o435d_s2_qra : QuotientRankAtLeast (o435SourceU ⟨2, by omega⟩) 16 :=
  quotientRankAtLeast_mono o435s2_sourceU_le_actual o435d_s2_qra_actual

-- Source 3: orbit144, lb=15, action, P=302, Q=477
private theorem o435d_s3_actual_le_transport :
    o435ActualSourceSpan ⟨3, by omega⟩ ≤
    actionW (codeMat 302) (codeMat 477) o144W := by
  apply o435_spanCodes_le_of_gens [262, 165, 100, 19, 10]
    (actionW (codeMat 302) (codeMat 477) o144W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 408 (by decide))
      (by unfold actionA; rw [o435_QtInv_477_431]
          show (codeMat 302 : Mat3).transpose * codeMat 408 * (codeMat 431 : Mat3).transpose = codeMat 262
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 85 (by decide))
      (by unfold actionA; rw [o435_QtInv_477_431]
          show (codeMat 302 : Mat3).transpose * codeMat 85 * (codeMat 431 : Mat3).transpose = codeMat 165
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 493 (by decide))
      (by unfold actionA; rw [o435_QtInv_477_431]
          show (codeMat 302 : Mat3).transpose * codeMat 493 * (codeMat 431 : Mat3).transpose = codeMat 100
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 462 (by decide))
      (by unfold actionA; rw [o435_QtInv_477_431]
          show (codeMat 302 : Mat3).transpose * codeMat 462 * (codeMat 431 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 119 (by decide))
      (by unfold actionA; rw [o435_QtInv_477_431]
          show (codeMat 302 : Mat3).transpose * codeMat 119 * (codeMat 431 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s3_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨3, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s3_actual_le_transport
    (o435_qra_action_code 302 477 (by decide) (by decide) step99_orbit144_lb15_unconditional)

private theorem o435d_s3_qra : QuotientRankAtLeast (o435SourceU ⟨3, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s3_sourceU_le_actual o435d_s3_qra_actual

-- Source 4: orbit144, lb=15, action, P=358, Q=474
private theorem o435d_s4_actual_le_transport :
    o435ActualSourceSpan ⟨4, by omega⟩ ≤
    actionW (codeMat 358) (codeMat 474) o144W := by
  apply o435_spanCodes_le_of_gens [256, 163, 98, 19, 10]
    (actionW (codeMat 358) (codeMat 474) o144W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 32 (by decide))
      (by unfold actionA; rw [o435_QtInv_474_395]
          show (codeMat 358 : Mat3).transpose * codeMat 32 * (codeMat 395 : Mat3).transpose = codeMat 256
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 84 (by decide))
      (by unfold actionA; rw [o435_QtInv_474_395]
          show (codeMat 358 : Mat3).transpose * codeMat 84 * (codeMat 395 : Mat3).transpose = codeMat 163
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 492 (by decide))
      (by unfold actionA; rw [o435_QtInv_474_395]
          show (codeMat 358 : Mat3).transpose * codeMat 492 * (codeMat 395 : Mat3).transpose = codeMat 98
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 119 (by decide))
      (by unfold actionA; rw [o435_QtInv_474_395]
          show (codeMat 358 : Mat3).transpose * codeMat 119 * (codeMat 395 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 462 (by decide))
      (by unfold actionA; rw [o435_QtInv_474_395]
          show (codeMat 358 : Mat3).transpose * codeMat 462 * (codeMat 395 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s4_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨4, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s4_actual_le_transport
    (o435_qra_action_code 358 474 (by decide) (by decide) step99_orbit144_lb15_unconditional)

private theorem o435d_s4_qra : QuotientRankAtLeast (o435SourceU ⟨4, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s4_sourceU_le_actual o435d_s4_qra_actual

-- Source 5: orbit196, lb=16, action, P=181, Q=188
private theorem o435d_s5_actual_le_transport :
    o435ActualSourceSpan ⟨5, by omega⟩ ≤
    actionW (codeMat 181) (codeMat 188) o196W := by
  apply o435_spanCodes_le_of_gens [291, 167, 102, 19, 10]
    (actionW (codeMat 181) (codeMat 188) o196W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 316 (by decide))
      (by unfold actionA; rw [o435_QtInv_188_103]
          show (codeMat 181 : Mat3).transpose * codeMat 316 * (codeMat 103 : Mat3).transpose = codeMat 291
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 143 (by decide))
      (by unfold actionA; rw [o435_QtInv_188_103]
          show (codeMat 181 : Mat3).transpose * codeMat 143 * (codeMat 103 : Mat3).transpose = codeMat 167
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 317 (by decide))
      (by unfold actionA; rw [o435_QtInv_188_103]
          show (codeMat 181 : Mat3).transpose * codeMat 317 * (codeMat 103 : Mat3).transpose = codeMat 102
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 164 (by decide))
      (by unfold actionA; rw [o435_QtInv_188_103]
          show (codeMat 181 : Mat3).transpose * codeMat 164 * (codeMat 103 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 310 (by decide))
      (by unfold actionA; rw [o435_QtInv_188_103]
          show (codeMat 181 : Mat3).transpose * codeMat 310 * (codeMat 103 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s5_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨5, by omega⟩) 16 :=
  quotientRankAtLeast_mono o435d_s5_actual_le_transport
    (o435_qra_action_code 181 188 (by decide) (by decide) step99_orbit196_lb16_unconditional)

private theorem o435d_s5_qra : QuotientRankAtLeast (o435SourceU ⟨5, by omega⟩) 16 :=
  quotientRankAtLeast_mono o435s5_sourceU_le_actual o435d_s5_qra_actual

-- Source 6: orbit144, lb=15, action, P=358, Q=254
private theorem o435d_s6_actual_le_transport :
    o435ActualSourceSpan ⟨6, by omega⟩ ≤
    actionW (codeMat 358) (codeMat 254) o144W := by
  apply o435_spanCodes_le_of_gens [288, 160, 97, 19, 10]
    (actionW (codeMat 358) (codeMat 254) o144W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 3 (by decide))
      (by unfold actionA; rw [o435_QtInv_254_443]
          show (codeMat 358 : Mat3).transpose * codeMat 3 * (codeMat 443 : Mat3).transpose = codeMat 288
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 35 (by decide))
      (by unfold actionA; rw [o435_QtInv_254_443]
          show (codeMat 358 : Mat3).transpose * codeMat 35 * (codeMat 443 : Mat3).transpose = codeMat 160
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 411 (by decide))
      (by unfold actionA; rw [o435_QtInv_254_443]
          show (codeMat 358 : Mat3).transpose * codeMat 411 * (codeMat 443 : Mat3).transpose = codeMat 97
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 119 (by decide))
      (by unfold actionA; rw [o435_QtInv_254_443]
          show (codeMat 358 : Mat3).transpose * codeMat 119 * (codeMat 443 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 462 (by decide))
      (by unfold actionA; rw [o435_QtInv_254_443]
          show (codeMat 358 : Mat3).transpose * codeMat 462 * (codeMat 443 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s6_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨6, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s6_actual_le_transport
    (o435_qra_action_code 358 254 (by decide) (by decide) step99_orbit144_lb15_unconditional)

private theorem o435d_s6_qra : QuotientRankAtLeast (o435SourceU ⟨6, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s6_sourceU_le_actual o435d_s6_qra_actual

-- Source 7: orbit196, lb=16, action, P=116, Q=412
private theorem o435d_s7_actual_le_transport :
    o435ActualSourceSpan ⟨7, by omega⟩ ≤
    actionW (codeMat 116) (codeMat 412) o196W := by
  apply o435_spanCodes_le_of_gens [257, 160, 97, 19, 10]
    (actionW (codeMat 116) (codeMat 412) o196W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 133 (by decide))
      (by unfold actionA; rw [o435_QtInv_412_111]
          show (codeMat 116 : Mat3).transpose * codeMat 133 * (codeMat 111 : Mat3).transpose = codeMat 257
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 43 (by decide))
      (by unfold actionA; rw [o435_QtInv_412_111]
          show (codeMat 116 : Mat3).transpose * codeMat 43 * (codeMat 111 : Mat3).transpose = codeMat 160
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 175 (by decide))
      (by unfold actionA; rw [o435_QtInv_412_111]
          show (codeMat 116 : Mat3).transpose * codeMat 175 * (codeMat 111 : Mat3).transpose = codeMat 97
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 310 (by decide))
      (by unfold actionA; rw [o435_QtInv_412_111]
          show (codeMat 116 : Mat3).transpose * codeMat 310 * (codeMat 111 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 402 (by decide))
      (by unfold actionA; rw [o435_QtInv_412_111]
          show (codeMat 116 : Mat3).transpose * codeMat 402 * (codeMat 111 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s7_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨7, by omega⟩) 16 :=
  quotientRankAtLeast_mono o435d_s7_actual_le_transport
    (o435_qra_action_code 116 412 (by decide) (by decide) step99_orbit196_lb16_unconditional)

private theorem o435d_s7_qra : QuotientRankAtLeast (o435SourceU ⟨7, by omega⟩) 16 :=
  quotientRankAtLeast_mono o435s7_sourceU_le_actual o435d_s7_qra_actual

-- Source 8: orbit196, lb=16, action, P=247, Q=444
private theorem o435d_s8_actual_le_transport :
    o435ActualSourceSpan ⟨8, by omega⟩ ≤
    actionW (codeMat 247) (codeMat 444) o196W := by
  apply o435_spanCodes_le_of_gens [289, 132, 69, 19, 10]
    (actionW (codeMat 247) (codeMat 444) o196W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 42 (by decide))
      (by unfold actionA; rw [o435_QtInv_444_110]
          show (codeMat 247 : Mat3).transpose * codeMat 42 * (codeMat 110 : Mat3).transpose = codeMat 289
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 441 (by decide))
      (by unfold actionA; rw [o435_QtInv_444_110]
          show (codeMat 247 : Mat3).transpose * codeMat 441 * (codeMat 110 : Mat3).transpose = codeMat 132
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 175 (by decide))
      (by unfold actionA; rw [o435_QtInv_444_110]
          show (codeMat 247 : Mat3).transpose * codeMat 175 * (codeMat 110 : Mat3).transpose = codeMat 69
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 402 (by decide))
      (by unfold actionA; rw [o435_QtInv_444_110]
          show (codeMat 247 : Mat3).transpose * codeMat 402 * (codeMat 110 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 164 (by decide))
      (by unfold actionA; rw [o435_QtInv_444_110]
          show (codeMat 247 : Mat3).transpose * codeMat 164 * (codeMat 110 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s8_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨8, by omega⟩) 16 :=
  quotientRankAtLeast_mono o435d_s8_actual_le_transport
    (o435_qra_action_code 247 444 (by decide) (by decide) step99_orbit196_lb16_unconditional)

private theorem o435d_s8_qra : QuotientRankAtLeast (o435SourceU ⟨8, by omega⟩) 16 :=
  quotientRankAtLeast_mono o435s8_sourceU_le_actual o435d_s8_qra_actual

-- Source 9: orbit144, lb=15, action, P=318, Q=478
private theorem o435d_s9_actual_le_transport :
    o435ActualSourceSpan ⟨9, by omega⟩ ≤
    actionW (codeMat 318) (codeMat 478) o144W := by
  apply o435_spanCodes_le_of_gens [295, 132, 69, 19, 10]
    (actionW (codeMat 318) (codeMat 478) o144W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 33 (by decide))
      (by unfold actionA; rw [o435_QtInv_478_445]
          show (codeMat 318 : Mat3).transpose * codeMat 33 * (codeMat 445 : Mat3).transpose = codeMat 295
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 493 (by decide))
      (by unfold actionA; rw [o435_QtInv_478_445]
          show (codeMat 318 : Mat3).transpose * codeMat 493 * (codeMat 445 : Mat3).transpose = codeMat 132
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 411 (by decide))
      (by unfold actionA; rw [o435_QtInv_478_445]
          show (codeMat 318 : Mat3).transpose * codeMat 411 * (codeMat 445 : Mat3).transpose = codeMat 69
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 462 (by decide))
      (by unfold actionA; rw [o435_QtInv_478_445]
          show (codeMat 318 : Mat3).transpose * codeMat 462 * (codeMat 445 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 441 (by decide))
      (by unfold actionA; rw [o435_QtInv_478_445]
          show (codeMat 318 : Mat3).transpose * codeMat 441 * (codeMat 445 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s9_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨9, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s9_actual_le_transport
    (o435_qra_action_code 318 478 (by decide) (by decide) step99_orbit144_lb15_unconditional)

private theorem o435d_s9_qra : QuotientRankAtLeast (o435SourceU ⟨9, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s9_sourceU_le_actual o435d_s9_qra_actual

-- Source 10: orbit144, lb=15, action, P=302, Q=253
private theorem o435d_s10_actual_le_transport :
    o435ActualSourceSpan ⟨10, by omega⟩ ≤
    actionW (codeMat 302) (codeMat 253) o144W := by
  apply o435_spanCodes_le_of_gens [288, 164, 101, 19, 10]
    (actionW (codeMat 302) (codeMat 253) o144W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 3 (by decide))
      (by unfold actionA; rw [o435_QtInv_253_415]
          show (codeMat 302 : Mat3).transpose * codeMat 3 * (codeMat 415 : Mat3).transpose = codeMat 288
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 411 (by decide))
      (by unfold actionA; rw [o435_QtInv_253_415]
          show (codeMat 302 : Mat3).transpose * codeMat 411 * (codeMat 415 : Mat3).transpose = codeMat 164
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 35 (by decide))
      (by unfold actionA; rw [o435_QtInv_253_415]
          show (codeMat 302 : Mat3).transpose * codeMat 35 * (codeMat 415 : Mat3).transpose = codeMat 101
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 462 (by decide))
      (by unfold actionA; rw [o435_QtInv_253_415]
          show (codeMat 302 : Mat3).transpose * codeMat 462 * (codeMat 415 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 119 (by decide))
      (by unfold actionA; rw [o435_QtInv_253_415]
          show (codeMat 302 : Mat3).transpose * codeMat 119 * (codeMat 415 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s10_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨10, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s10_actual_le_transport
    (o435_qra_action_code 302 253 (by decide) (by decide) step99_orbit144_lb15_unconditional)

private theorem o435d_s10_qra : QuotientRankAtLeast (o435SourceU ⟨10, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s10_sourceU_le_actual o435d_s10_qra_actual

-- Source 11: orbit196, lb=16, action, P=181, Q=156
private theorem o435d_s11_actual_le_transport :
    o435ActualSourceSpan ⟨11, by omega⟩ ≤
    actionW (codeMat 181) (codeMat 156) o196W := by
  apply o435_spanCodes_le_of_gens [260, 164, 101, 19, 10]
    (actionW (codeMat 181) (codeMat 156) o196W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 1 (by decide))
      (by unfold actionA; rw [o435_QtInv_156_102]
          show (codeMat 181 : Mat3).transpose * codeMat 1 * (codeMat 102 : Mat3).transpose = codeMat 260
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 441 (by decide))
      (by unfold actionA; rw [o435_QtInv_156_102]
          show (codeMat 181 : Mat3).transpose * codeMat 441 * (codeMat 102 : Mat3).transpose = codeMat 164
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 11 (by decide))
      (by unfold actionA; rw [o435_QtInv_156_102]
          show (codeMat 181 : Mat3).transpose * codeMat 11 * (codeMat 102 : Mat3).transpose = codeMat 101
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 164 (by decide))
      (by unfold actionA; rw [o435_QtInv_156_102]
          show (codeMat 181 : Mat3).transpose * codeMat 164 * (codeMat 102 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 310 (by decide))
      (by unfold actionA; rw [o435_QtInv_156_102]
          show (codeMat 181 : Mat3).transpose * codeMat 310 * (codeMat 102 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s11_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨11, by omega⟩) 16 :=
  quotientRankAtLeast_mono o435d_s11_actual_le_transport
    (o435_qra_action_code 181 156 (by decide) (by decide) step99_orbit196_lb16_unconditional)

private theorem o435d_s11_qra : QuotientRankAtLeast (o435SourceU ⟨11, by omega⟩) 16 :=
  quotientRankAtLeast_mono o435s11_sourceU_le_actual o435d_s11_qra_actual

-- Source 12: orbit144, lb=15, action, P=318, Q=250
private theorem o435d_s12_actual_le_transport :
    o435ActualSourceSpan ⟨12, by omega⟩ ≤
    actionW (codeMat 318) (codeMat 250) o144W := by
  apply o435_spanCodes_le_of_gens [288, 134, 71, 19, 10]
    (actionW (codeMat 318) (codeMat 250) o144W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 2 (by decide))
      (by unfold actionA; rw [o435_QtInv_250_397]
          show (codeMat 318 : Mat3).transpose * codeMat 2 * (codeMat 397 : Mat3).transpose = codeMat 288
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 493 (by decide))
      (by unfold actionA; rw [o435_QtInv_250_397]
          show (codeMat 318 : Mat3).transpose * codeMat 493 * (codeMat 397 : Mat3).transpose = codeMat 134
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 411 (by decide))
      (by unfold actionA; rw [o435_QtInv_250_397]
          show (codeMat 318 : Mat3).transpose * codeMat 411 * (codeMat 397 : Mat3).transpose = codeMat 71
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 462 (by decide))
      (by unfold actionA; rw [o435_QtInv_250_397]
          show (codeMat 318 : Mat3).transpose * codeMat 462 * (codeMat 397 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 441 (by decide))
      (by unfold actionA; rw [o435_QtInv_250_397]
          show (codeMat 318 : Mat3).transpose * codeMat 441 * (codeMat 397 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s12_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨12, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s12_actual_le_transport
    (o435_qra_action_code 318 250 (by decide) (by decide) step99_orbit144_lb15_unconditional)

private theorem o435d_s12_qra : QuotientRankAtLeast (o435SourceU ⟨12, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s12_sourceU_le_actual o435d_s12_qra_actual

-- Source 13: orbit144, lb=15, action, P=302, Q=249
private theorem o435d_s13_actual_le_transport :
    o435ActualSourceSpan ⟨13, by omega⟩ ≤
    actionW (codeMat 302) (codeMat 249) o144W := by
  apply o435_spanCodes_le_of_gens [288, 166, 103, 19, 10]
    (actionW (codeMat 302) (codeMat 249) o144W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 2 (by decide))
      (by unfold actionA; rw [o435_QtInv_249_425]
          show (codeMat 302 : Mat3).transpose * codeMat 2 * (codeMat 425 : Mat3).transpose = codeMat 288
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 34 (by decide))
      (by unfold actionA; rw [o435_QtInv_249_425]
          show (codeMat 302 : Mat3).transpose * codeMat 34 * (codeMat 425 : Mat3).transpose = codeMat 166
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 410 (by decide))
      (by unfold actionA; rw [o435_QtInv_249_425]
          show (codeMat 302 : Mat3).transpose * codeMat 410 * (codeMat 425 : Mat3).transpose = codeMat 103
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 462 (by decide))
      (by unfold actionA; rw [o435_QtInv_249_425]
          show (codeMat 302 : Mat3).transpose * codeMat 462 * (codeMat 425 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 119 (by decide))
      (by unfold actionA; rw [o435_QtInv_249_425]
          show (codeMat 302 : Mat3).transpose * codeMat 119 * (codeMat 425 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s13_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨13, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s13_actual_le_transport
    (o435_qra_action_code 302 249 (by decide) (by decide) step99_orbit144_lb15_unconditional)

private theorem o435d_s13_qra : QuotientRankAtLeast (o435SourceU ⟨13, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s13_sourceU_le_actual o435d_s13_qra_actual

-- Source 14: orbit95, lb=15, transpose_after_action, P=266, Q=394
private theorem o435d_s14_actual_le_transport :
    o435ActualSourceSpan ⟨14, by omega⟩ ≤
    transposeW (actionW (codeMat 266) (codeMat 394) o95W_mono) := by
  apply o435_spanCodes_le_of_gens [129, 64, 17, 8, 2]
    (transposeW (actionW (codeMat 266) (codeMat 394) o95W_mono))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    exact ⟨codeMat 33,
      o435_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [32, 20, 8, 2, 1] 20 (by decide))
        (by unfold actionA; rw [o435_QtInv_394_330]
            show (codeMat 266 : Mat3).transpose * codeMat 20 * (codeMat 330 : Mat3).transpose = codeMat 33
            ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h1
    exact ⟨codeMat 4,
      o435_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [32, 20, 8, 2, 1] 32 (by decide))
        (by unfold actionA; rw [o435_QtInv_394_330]
            show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 330 : Mat3).transpose = codeMat 4
            ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h2
    exact ⟨codeMat 17,
      o435_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [32, 20, 8, 2, 1] 21 (by decide))
        (by unfold actionA; rw [o435_QtInv_394_330]
            show (codeMat 266 : Mat3).transpose * codeMat 21 * (codeMat 330 : Mat3).transpose = codeMat 17
            ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h3
    exact ⟨codeMat 2,
      o435_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [32, 20, 8, 2, 1] 40 (by decide))
        (by unfold actionA; rw [o435_QtInv_394_330]
            show (codeMat 266 : Mat3).transpose * codeMat 40 * (codeMat 330 : Mat3).transpose = codeMat 2
            ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h4
    exact ⟨codeMat 8,
      o435_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [32, 20, 8, 2, 1] 2 (by decide))
        (by unfold actionA; rw [o435_QtInv_394_330]
            show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 330 : Mat3).transpose = codeMat 8
            ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩

private theorem o435d_s14_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨14, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s14_actual_le_transport
    (quotientRankAtLeast_transpose (o435_qra_action_code 266 394 (by decide) (by decide) orbit95_lb15_mono))

private theorem o435d_s14_qra : QuotientRankAtLeast (o435SourceU ⟨14, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s14_sourceU_le_actual o435d_s14_qra_actual

-- Source 15: orbit95, lb=15, transpose_after_action, P=266, Q=122
private theorem o435d_s15_actual_le_transport :
    o435ActualSourceSpan ⟨15, by omega⟩ ≤
    transposeW (actionW (codeMat 266) (codeMat 122) o95W_mono) := by
  apply o435_spanCodes_le_of_gens [128, 65, 16, 9, 3]
    (transposeW (actionW (codeMat 266) (codeMat 122) o95W_mono))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    exact ⟨codeMat 32,
      o435_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [32, 20, 8, 2, 1] 2 (by decide))
        (by unfold actionA; rw [o435_QtInv_122_460]
            show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 460 : Mat3).transpose = codeMat 32
            ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h1
    exact ⟨codeMat 5,
      o435_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [32, 20, 8, 2, 1] 32 (by decide))
        (by unfold actionA; rw [o435_QtInv_122_460]
            show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 460 : Mat3).transpose = codeMat 5
            ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h2
    exact ⟨codeMat 16,
      o435_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [32, 20, 8, 2, 1] 3 (by decide))
        (by unfold actionA; rw [o435_QtInv_122_460]
            show (codeMat 266 : Mat3).transpose * codeMat 3 * (codeMat 460 : Mat3).transpose = codeMat 16
            ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h3
    exact ⟨codeMat 3,
      o435_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [32, 20, 8, 2, 1] 40 (by decide))
        (by unfold actionA; rw [o435_QtInv_122_460]
            show (codeMat 266 : Mat3).transpose * codeMat 40 * (codeMat 460 : Mat3).transpose = codeMat 3
            ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h4
    exact ⟨codeMat 9,
      o435_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [32, 20, 8, 2, 1] 54 (by decide))
        (by unfold actionA; rw [o435_QtInv_122_460]
            show (codeMat 266 : Mat3).transpose * codeMat 54 * (codeMat 460 : Mat3).transpose = codeMat 9
            ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩

private theorem o435d_s15_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨15, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s15_actual_le_transport
    (quotientRankAtLeast_transpose (o435_qra_action_code 266 122 (by decide) (by decide) orbit95_lb15_mono))

private theorem o435d_s15_qra : QuotientRankAtLeast (o435SourceU ⟨15, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s15_sourceU_le_actual o435d_s15_qra_actual

-- Source 16: orbit95, lb=15, transpose_after_action, P=266, Q=498
private theorem o435d_s16_actual_le_transport :
    o435ActualSourceSpan ⟨16, by omega⟩ ≤
    transposeW (actionW (codeMat 266) (codeMat 498) o95W_mono) := by
  apply o435_spanCodes_le_of_gens [130, 66, 18, 10, 1]
    (transposeW (actionW (codeMat 266) (codeMat 498) o95W_mono))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    exact ⟨codeMat 40,
      o435_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [32, 20, 8, 2, 1] 2 (by decide))
        (by unfold actionA; rw [o435_QtInv_498_206]
            show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 206 : Mat3).transpose = codeMat 40
            ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h1
    exact ⟨codeMat 12,
      o435_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [32, 20, 8, 2, 1] 52 (by decide))
        (by unfold actionA; rw [o435_QtInv_498_206]
            show (codeMat 266 : Mat3).transpose * codeMat 52 * (codeMat 206 : Mat3).transpose = codeMat 12
            ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h2
    exact ⟨codeMat 24,
      o435_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [32, 20, 8, 2, 1] 3 (by decide))
        (by unfold actionA; rw [o435_QtInv_498_206]
            show (codeMat 266 : Mat3).transpose * codeMat 3 * (codeMat 206 : Mat3).transpose = codeMat 24
            ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h3
    exact ⟨codeMat 10,
      o435_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [32, 20, 8, 2, 1] 60 (by decide))
        (by unfold actionA; rw [o435_QtInv_498_206]
            show (codeMat 266 : Mat3).transpose * codeMat 60 * (codeMat 206 : Mat3).transpose = codeMat 10
            ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h4
    exact ⟨codeMat 1,
      o435_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [32, 20, 8, 2, 1] 32 (by decide))
        (by unfold actionA; rw [o435_QtInv_498_206]
            show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 206 : Mat3).transpose = codeMat 1
            ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩

private theorem o435d_s16_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨16, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s16_actual_le_transport
    (quotientRankAtLeast_transpose (o435_qra_action_code 266 498 (by decide) (by decide) orbit95_lb15_mono))

private theorem o435d_s16_qra : QuotientRankAtLeast (o435SourceU ⟨16, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s16_sourceU_le_actual o435d_s16_qra_actual

-- Source 17: orbit158, lb=15, action, P=394, Q=465
private theorem o435d_s17_actual_le_transport :
    o435ActualSourceSpan ⟨17, by omega⟩ ≤
    actionW (codeMat 394) (codeMat 465) o158W_mono := by
  apply o435_spanCodes_le_of_gens [193, 34, 19, 10, 4]
    (actionW (codeMat 394) (codeMat 465) o158W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [192, 32, 20, 10, 1] 235 (by decide))
      (by unfold actionA; rw [o435_QtInv_465_465]
          show (codeMat 394 : Mat3).transpose * codeMat 235 * (codeMat 465 : Mat3).transpose = codeMat 193
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [192, 32, 20, 10, 1] 52 (by decide))
      (by unfold actionA; rw [o435_QtInv_465_465]
          show (codeMat 394 : Mat3).transpose * codeMat 52 * (codeMat 465 : Mat3).transpose = codeMat 34
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [192, 32, 20, 10, 1] 30 (by decide))
      (by unfold actionA; rw [o435_QtInv_465_465]
          show (codeMat 394 : Mat3).transpose * codeMat 30 * (codeMat 465 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [192, 32, 20, 10, 1] 53 (by decide))
      (by unfold actionA; rw [o435_QtInv_465_465]
          show (codeMat 394 : Mat3).transpose * codeMat 53 * (codeMat 465 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [192, 32, 20, 10, 1] 32 (by decide))
      (by unfold actionA; rw [o435_QtInv_465_465]
          show (codeMat 394 : Mat3).transpose * codeMat 32 * (codeMat 465 : Mat3).transpose = codeMat 4
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s17_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨17, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s17_actual_le_transport
    (o435_qra_action_code 394 465 (by decide) (by decide) orbit158_lb15_mono)

private theorem o435d_s17_qra : QuotientRankAtLeast (o435SourceU ⟨17, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s17_sourceU_le_actual o435d_s17_qra_actual

-- Source 18: orbit158, lb=15, action, P=395, Q=458
private theorem o435d_s18_actual_le_transport :
    o435ActualSourceSpan ⟨18, by omega⟩ ≤
    actionW (codeMat 395) (codeMat 458) o158W_mono := by
  apply o435_spanCodes_le_of_gens [193, 33, 19, 10, 4]
    (actionW (codeMat 395) (codeMat 458) o158W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [192, 32, 20, 10, 1] 235 (by decide))
      (by unfold actionA; rw [o435_QtInv_458_458]
          show (codeMat 395 : Mat3).transpose * codeMat 235 * (codeMat 458 : Mat3).transpose = codeMat 193
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [192, 32, 20, 10, 1] 20 (by decide))
      (by unfold actionA; rw [o435_QtInv_458_458]
          show (codeMat 395 : Mat3).transpose * codeMat 20 * (codeMat 458 : Mat3).transpose = codeMat 33
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [192, 32, 20, 10, 1] 53 (by decide))
      (by unfold actionA; rw [o435_QtInv_458_458]
          show (codeMat 395 : Mat3).transpose * codeMat 53 * (codeMat 458 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [192, 32, 20, 10, 1] 30 (by decide))
      (by unfold actionA; rw [o435_QtInv_458_458]
          show (codeMat 395 : Mat3).transpose * codeMat 30 * (codeMat 458 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [192, 32, 20, 10, 1] 32 (by decide))
      (by unfold actionA; rw [o435_QtInv_458_458]
          show (codeMat 395 : Mat3).transpose * codeMat 32 * (codeMat 458 : Mat3).transpose = codeMat 4
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s18_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨18, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s18_actual_le_transport
    (o435_qra_action_code 395 458 (by decide) (by decide) orbit158_lb15_mono)

private theorem o435d_s18_qra : QuotientRankAtLeast (o435SourceU ⟨18, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s18_sourceU_le_actual o435d_s18_qra_actual

-- Source 19: orbit158, lb=15, action, P=395, Q=206
private theorem o435d_s19_actual_le_transport :
    o435ActualSourceSpan ⟨19, by omega⟩ ≤
    actionW (codeMat 395) (codeMat 206) o158W_mono := by
  apply o435_spanCodes_le_of_gens [193, 34, 19, 10, 6]
    (actionW (codeMat 395) (codeMat 206) o158W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [192, 32, 20, 10, 1] 235 (by decide))
      (by unfold actionA; rw [o435_QtInv_206_498]
          show (codeMat 395 : Mat3).transpose * codeMat 235 * (codeMat 498 : Mat3).transpose = codeMat 193
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [192, 32, 20, 10, 1] 33 (by decide))
      (by unfold actionA; rw [o435_QtInv_206_498]
          show (codeMat 395 : Mat3).transpose * codeMat 33 * (codeMat 498 : Mat3).transpose = codeMat 34
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [192, 32, 20, 10, 1] 53 (by decide))
      (by unfold actionA; rw [o435_QtInv_206_498]
          show (codeMat 395 : Mat3).transpose * codeMat 53 * (codeMat 498 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [192, 32, 20, 10, 1] 30 (by decide))
      (by unfold actionA; rw [o435_QtInv_206_498]
          show (codeMat 395 : Mat3).transpose * codeMat 30 * (codeMat 498 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [192, 32, 20, 10, 1] 32 (by decide))
      (by unfold actionA; rw [o435_QtInv_206_498]
          show (codeMat 395 : Mat3).transpose * codeMat 32 * (codeMat 498 : Mat3).transpose = codeMat 6
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s19_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨19, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s19_actual_le_transport
    (o435_qra_action_code 395 206 (by decide) (by decide) orbit158_lb15_mono)

private theorem o435d_s19_qra : QuotientRankAtLeast (o435SourceU ⟨19, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s19_sourceU_le_actual o435d_s19_qra_actual

-- Source 20: orbit158, lb=15, action, P=401, Q=494
private theorem o435d_s20_actual_le_transport :
    o435ActualSourceSpan ⟨20, by omega⟩ ≤
    actionW (codeMat 401) (codeMat 494) o158W_mono := by
  apply o435_spanCodes_le_of_gens [193, 33, 19, 10, 5]
    (actionW (codeMat 401) (codeMat 494) o158W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [192, 32, 20, 10, 1] 222 (by decide))
      (by unfold actionA; rw [o435_QtInv_494_501]
          show (codeMat 401 : Mat3).transpose * codeMat 222 * (codeMat 501 : Mat3).transpose = codeMat 193
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [192, 32, 20, 10, 1] 62 (by decide))
      (by unfold actionA; rw [o435_QtInv_494_501]
          show (codeMat 401 : Mat3).transpose * codeMat 62 * (codeMat 501 : Mat3).transpose = codeMat 33
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [192, 32, 20, 10, 1] 43 (by decide))
      (by unfold actionA; rw [o435_QtInv_494_501]
          show (codeMat 401 : Mat3).transpose * codeMat 43 * (codeMat 501 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [192, 32, 20, 10, 1] 53 (by decide))
      (by unfold actionA; rw [o435_QtInv_494_501]
          show (codeMat 401 : Mat3).transpose * codeMat 53 * (codeMat 501 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [192, 32, 20, 10, 1] 1 (by decide))
      (by unfold actionA; rw [o435_QtInv_494_501]
          show (codeMat 401 : Mat3).transpose * codeMat 1 * (codeMat 501 : Mat3).transpose = codeMat 5
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s20_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨20, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s20_actual_le_transport
    (o435_qra_action_code 401 494 (by decide) (by decide) orbit158_lb15_mono)

private theorem o435d_s20_qra : QuotientRankAtLeast (o435SourceU ⟨20, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s20_sourceU_le_actual o435d_s20_qra_actual

-- Source 21: orbit158, lb=15, action, P=395, Q=234
private theorem o435d_s21_actual_le_transport :
    o435ActualSourceSpan ⟨21, by omega⟩ ≤
    actionW (codeMat 395) (codeMat 234) o158W_mono := by
  apply o435_spanCodes_le_of_gens [193, 35, 19, 10, 5]
    (actionW (codeMat 395) (codeMat 234) o158W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [192, 32, 20, 10, 1] 235 (by decide))
      (by unfold actionA; rw [o435_QtInv_234_461]
          show (codeMat 395 : Mat3).transpose * codeMat 235 * (codeMat 461 : Mat3).transpose = codeMat 193
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [192, 32, 20, 10, 1] 10 (by decide))
      (by unfold actionA; rw [o435_QtInv_234_461]
          show (codeMat 395 : Mat3).transpose * codeMat 10 * (codeMat 461 : Mat3).transpose = codeMat 35
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [192, 32, 20, 10, 1] 53 (by decide))
      (by unfold actionA; rw [o435_QtInv_234_461]
          show (codeMat 395 : Mat3).transpose * codeMat 53 * (codeMat 461 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [192, 32, 20, 10, 1] 30 (by decide))
      (by unfold actionA; rw [o435_QtInv_234_461]
          show (codeMat 395 : Mat3).transpose * codeMat 30 * (codeMat 461 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [192, 32, 20, 10, 1] 32 (by decide))
      (by unfold actionA; rw [o435_QtInv_234_461]
          show (codeMat 395 : Mat3).transpose * codeMat 32 * (codeMat 461 : Mat3).transpose = codeMat 5
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s21_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨21, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s21_actual_le_transport
    (o435_qra_action_code 395 234 (by decide) (by decide) orbit158_lb15_mono)

private theorem o435d_s21_qra : QuotientRankAtLeast (o435SourceU ⟨21, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s21_sourceU_le_actual o435d_s21_qra_actual

-- Source 22: orbit158, lb=15, action, P=395, Q=494
private theorem o435d_s22_actual_le_transport :
    o435ActualSourceSpan ⟨22, by omega⟩ ≤
    actionW (codeMat 395) (codeMat 494) o158W_mono := by
  apply o435_spanCodes_le_of_gens [193, 32, 19, 10, 7]
    (actionW (codeMat 395) (codeMat 494) o158W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [192, 32, 20, 10, 1] 235 (by decide))
      (by unfold actionA; rw [o435_QtInv_494_501]
          show (codeMat 395 : Mat3).transpose * codeMat 235 * (codeMat 501 : Mat3).transpose = codeMat 193
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [192, 32, 20, 10, 1] 63 (by decide))
      (by unfold actionA; rw [o435_QtInv_494_501]
          show (codeMat 395 : Mat3).transpose * codeMat 63 * (codeMat 501 : Mat3).transpose = codeMat 32
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [192, 32, 20, 10, 1] 53 (by decide))
      (by unfold actionA; rw [o435_QtInv_494_501]
          show (codeMat 395 : Mat3).transpose * codeMat 53 * (codeMat 501 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [192, 32, 20, 10, 1] 30 (by decide))
      (by unfold actionA; rw [o435_QtInv_494_501]
          show (codeMat 395 : Mat3).transpose * codeMat 30 * (codeMat 501 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [192, 32, 20, 10, 1] 32 (by decide))
      (by unfold actionA; rw [o435_QtInv_494_501]
          show (codeMat 395 : Mat3).transpose * codeMat 32 * (codeMat 501 : Mat3).transpose = codeMat 7
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s22_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨22, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s22_actual_le_transport
    (o435_qra_action_code 395 494 (by decide) (by decide) orbit158_lb15_mono)

private theorem o435d_s22_qra : QuotientRankAtLeast (o435SourceU ⟨22, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s22_sourceU_le_actual o435d_s22_qra_actual

-- Source 23: orbit158, lb=15, action, P=394, Q=501
private theorem o435d_s23_actual_le_transport :
    o435ActualSourceSpan ⟨23, by omega⟩ ≤
    actionW (codeMat 394) (codeMat 501) o158W_mono := by
  apply o435_spanCodes_le_of_gens [193, 35, 19, 10, 7]
    (actionW (codeMat 394) (codeMat 501) o158W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [192, 32, 20, 10, 1] 235 (by decide))
      (by unfold actionA; rw [o435_QtInv_501_494]
          show (codeMat 394 : Mat3).transpose * codeMat 235 * (codeMat 494 : Mat3).transpose = codeMat 193
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [192, 32, 20, 10, 1] 31 (by decide))
      (by unfold actionA; rw [o435_QtInv_501_494]
          show (codeMat 394 : Mat3).transpose * codeMat 31 * (codeMat 494 : Mat3).transpose = codeMat 35
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [192, 32, 20, 10, 1] 30 (by decide))
      (by unfold actionA; rw [o435_QtInv_501_494]
          show (codeMat 394 : Mat3).transpose * codeMat 30 * (codeMat 494 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [192, 32, 20, 10, 1] 53 (by decide))
      (by unfold actionA; rw [o435_QtInv_501_494]
          show (codeMat 394 : Mat3).transpose * codeMat 53 * (codeMat 494 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [192, 32, 20, 10, 1] 32 (by decide))
      (by unfold actionA; rw [o435_QtInv_501_494]
          show (codeMat 394 : Mat3).transpose * codeMat 32 * (codeMat 494 : Mat3).transpose = codeMat 7
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s23_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨23, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s23_actual_le_transport
    (o435_qra_action_code 394 501 (by decide) (by decide) orbit158_lb15_mono)

private theorem o435d_s23_qra : QuotientRankAtLeast (o435SourceU ⟨23, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s23_sourceU_le_actual o435d_s23_qra_actual

-- Source 24: orbit69, lb=15, action, P=470, Q=249
private theorem o435d_s24_actual_le_transport :
    o435ActualSourceSpan ⟨24, by omega⟩ ≤
    actionW (codeMat 470) (codeMat 249) o69W := by
  apply o435_spanCodes_le_of_gens [257, 132, 69, 32, 19, 10]
    (actionW (codeMat 470) (codeMat 249) o69W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 469 (by decide))
      (by unfold actionA; rw [o435_QtInv_249_425]
          show (codeMat 470 : Mat3).transpose * codeMat 469 * (codeMat 425 : Mat3).transpose = codeMat 257
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 180 (by decide))
      (by unfold actionA; rw [o435_QtInv_249_425]
          show (codeMat 470 : Mat3).transpose * codeMat 180 * (codeMat 425 : Mat3).transpose = codeMat 132
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 378 (by decide))
      (by unfold actionA; rw [o435_QtInv_249_425]
          show (codeMat 470 : Mat3).transpose * codeMat 378 * (codeMat 425 : Mat3).transpose = codeMat 69
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 16 (by decide))
      (by unfold actionA; rw [o435_QtInv_249_425]
          show (codeMat 470 : Mat3).transpose * codeMat 16 * (codeMat 425 : Mat3).transpose = codeMat 32
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 113 (by decide))
      (by unfold actionA; rw [o435_QtInv_249_425]
          show (codeMat 470 : Mat3).transpose * codeMat 113 * (codeMat 425 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 446 (by decide))
      (by unfold actionA; rw [o435_QtInv_249_425]
          show (codeMat 470 : Mat3).transpose * codeMat 446 * (codeMat 425 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s24_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨24, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s24_actual_le_transport
    (o435_qra_action_code 470 249 (by decide) (by decide) step99_orbit69_lb15_unconditional)

private theorem o435d_s24_qra : QuotientRankAtLeast (o435SourceU ⟨24, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s24_sourceU_le_actual o435d_s24_qra_actual

-- Source 25: orbit69, lb=15, action, P=286, Q=249
private theorem o435d_s25_actual_le_transport :
    o435ActualSourceSpan ⟨25, by omega⟩ ≤
    actionW (codeMat 286) (codeMat 249) o69W := by
  apply o435_spanCodes_le_of_gens [262, 134, 71, 36, 19, 10]
    (actionW (codeMat 286) (codeMat 249) o69W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 420 (by decide))
      (by unfold actionA; rw [o435_QtInv_249_425]
          show (codeMat 286 : Mat3).transpose * codeMat 420 * (codeMat 425 : Mat3).transpose = codeMat 262
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 164 (by decide))
      (by unfold actionA; rw [o435_QtInv_249_425]
          show (codeMat 286 : Mat3).transpose * codeMat 164 * (codeMat 425 : Mat3).transpose = codeMat 134
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 283 (by decide))
      (by unfold actionA; rw [o435_QtInv_249_425]
          show (codeMat 286 : Mat3).transpose * codeMat 283 * (codeMat 425 : Mat3).transpose = codeMat 71
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 16 (by decide))
      (by unfold actionA; rw [o435_QtInv_249_425]
          show (codeMat 286 : Mat3).transpose * codeMat 16 * (codeMat 425 : Mat3).transpose = codeMat 36
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 463 (by decide))
      (by unfold actionA; rw [o435_QtInv_249_425]
          show (codeMat 286 : Mat3).transpose * codeMat 463 * (codeMat 425 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 113 (by decide))
      (by unfold actionA; rw [o435_QtInv_249_425]
          show (codeMat 286 : Mat3).transpose * codeMat 113 * (codeMat 425 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s25_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨25, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s25_actual_le_transport
    (o435_qra_action_code 286 249 (by decide) (by decide) step99_orbit69_lb15_unconditional)

private theorem o435d_s25_qra : QuotientRankAtLeast (o435SourceU ⟨25, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s25_sourceU_le_actual o435d_s25_qra_actual

-- Source 26: orbit69, lb=15, action, P=470, Q=477
private theorem o435d_s26_actual_le_transport :
    o435ActualSourceSpan ⟨26, by omega⟩ ≤
    actionW (codeMat 470) (codeMat 477) o69W := by
  apply o435_spanCodes_le_of_gens [261, 133, 68, 34, 19, 10]
    (actionW (codeMat 470) (codeMat 477) o69W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 175 (by decide))
      (by unfold actionA; rw [o435_QtInv_477_431]
          show (codeMat 470 : Mat3).transpose * codeMat 175 * (codeMat 431 : Mat3).transpose = codeMat 261
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 180 (by decide))
      (by unfold actionA; rw [o435_QtInv_477_431]
          show (codeMat 470 : Mat3).transpose * codeMat 180 * (codeMat 431 : Mat3).transpose = codeMat 133
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 378 (by decide))
      (by unfold actionA; rw [o435_QtInv_477_431]
          show (codeMat 470 : Mat3).transpose * codeMat 378 * (codeMat 431 : Mat3).transpose = codeMat 68
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 430 (by decide))
      (by unfold actionA; rw [o435_QtInv_477_431]
          show (codeMat 470 : Mat3).transpose * codeMat 430 * (codeMat 431 : Mat3).transpose = codeMat 34
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 113 (by decide))
      (by unfold actionA; rw [o435_QtInv_477_431]
          show (codeMat 470 : Mat3).transpose * codeMat 113 * (codeMat 431 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 446 (by decide))
      (by unfold actionA; rw [o435_QtInv_477_431]
          show (codeMat 470 : Mat3).transpose * codeMat 446 * (codeMat 431 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s26_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨26, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s26_actual_le_transport
    (o435_qra_action_code 470 477 (by decide) (by decide) step99_orbit69_lb15_unconditional)

private theorem o435d_s26_qra : QuotientRankAtLeast (o435SourceU ⟨26, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s26_sourceU_le_actual o435d_s26_qra_actual

-- Source 27: orbit69, lb=15, action, P=342, Q=474
private theorem o435d_s27_actual_le_transport :
    o435ActualSourceSpan ⟨27, by omega⟩ ≤
    actionW (codeMat 342) (codeMat 474) o69W := by
  apply o435_spanCodes_le_of_gens [260, 132, 69, 34, 19, 10]
    (actionW (codeMat 342) (codeMat 474) o69W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 256 (by decide))
      (by unfold actionA; rw [o435_QtInv_474_395]
          show (codeMat 342 : Mat3).transpose * codeMat 256 * (codeMat 395 : Mat3).transpose = codeMat 260
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 283 (by decide))
      (by unfold actionA; rw [o435_QtInv_474_395]
          show (codeMat 342 : Mat3).transpose * codeMat 283 * (codeMat 395 : Mat3).transpose = codeMat 132
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 164 (by decide))
      (by unfold actionA; rw [o435_QtInv_474_395]
          show (codeMat 342 : Mat3).transpose * codeMat 164 * (codeMat 395 : Mat3).transpose = codeMat 69
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 479 (by decide))
      (by unfold actionA; rw [o435_QtInv_474_395]
          show (codeMat 342 : Mat3).transpose * codeMat 479 * (codeMat 395 : Mat3).transpose = codeMat 34
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 113 (by decide))
      (by unfold actionA; rw [o435_QtInv_474_395]
          show (codeMat 342 : Mat3).transpose * codeMat 113 * (codeMat 395 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 463 (by decide))
      (by unfold actionA; rw [o435_QtInv_474_395]
          show (codeMat 342 : Mat3).transpose * codeMat 463 * (codeMat 395 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s27_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨27, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s27_actual_le_transport
    (o435_qra_action_code 342 474 (by decide) (by decide) step99_orbit69_lb15_unconditional)

private theorem o435d_s27_qra : QuotientRankAtLeast (o435SourceU ⟨27, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s27_sourceU_le_actual o435d_s27_qra_actual

-- Source 28: orbit69, lb=15, action, P=286, Q=253
private theorem o435d_s28_actual_le_transport :
    o435ActualSourceSpan ⟨28, by omega⟩ ≤
    actionW (codeMat 286) (codeMat 253) o69W := by
  apply o435_spanCodes_le_of_gens [260, 133, 68, 38, 19, 10]
    (actionW (codeMat 286) (codeMat 253) o69W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 27 (by decide))
      (by unfold actionA; rw [o435_QtInv_253_415]
          show (codeMat 286 : Mat3).transpose * codeMat 27 * (codeMat 415 : Mat3).transpose = codeMat 260
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 164 (by decide))
      (by unfold actionA; rw [o435_QtInv_253_415]
          show (codeMat 286 : Mat3).transpose * codeMat 164 * (codeMat 415 : Mat3).transpose = codeMat 133
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 283 (by decide))
      (by unfold actionA; rw [o435_QtInv_253_415]
          show (codeMat 286 : Mat3).transpose * codeMat 283 * (codeMat 415 : Mat3).transpose = codeMat 68
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 430 (by decide))
      (by unfold actionA; rw [o435_QtInv_253_415]
          show (codeMat 286 : Mat3).transpose * codeMat 430 * (codeMat 415 : Mat3).transpose = codeMat 38
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 463 (by decide))
      (by unfold actionA; rw [o435_QtInv_253_415]
          show (codeMat 286 : Mat3).transpose * codeMat 463 * (codeMat 415 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 113 (by decide))
      (by unfold actionA; rw [o435_QtInv_253_415]
          show (codeMat 286 : Mat3).transpose * codeMat 113 * (codeMat 415 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s28_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨28, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s28_actual_le_transport
    (o435_qra_action_code 286 253 (by decide) (by decide) step99_orbit69_lb15_unconditional)

private theorem o435d_s28_qra : QuotientRankAtLeast (o435SourceU ⟨28, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s28_sourceU_le_actual o435d_s28_qra_actual

-- Source 29: orbit69, lb=15, action, P=478, Q=254
private theorem o435d_s29_actual_le_transport :
    o435ActualSourceSpan ⟨29, by omega⟩ ≤
    actionW (codeMat 478) (codeMat 254) o69W := by
  apply o435_spanCodes_le_of_gens [260, 135, 70, 38, 19, 10]
    (actionW (codeMat 478) (codeMat 254) o69W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 27 (by decide))
      (by unfold actionA; rw [o435_QtInv_254_443]
          show (codeMat 478 : Mat3).transpose * codeMat 27 * (codeMat 443 : Mat3).transpose = codeMat 260
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 378 (by decide))
      (by unfold actionA; rw [o435_QtInv_254_443]
          show (codeMat 478 : Mat3).transpose * codeMat 378 * (codeMat 443 : Mat3).transpose = codeMat 135
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 180 (by decide))
      (by unfold actionA; rw [o435_QtInv_254_443]
          show (codeMat 478 : Mat3).transpose * codeMat 180 * (codeMat 443 : Mat3).transpose = codeMat 70
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 479 (by decide))
      (by unfold actionA; rw [o435_QtInv_254_443]
          show (codeMat 478 : Mat3).transpose * codeMat 479 * (codeMat 443 : Mat3).transpose = codeMat 38
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 446 (by decide))
      (by unfold actionA; rw [o435_QtInv_254_443]
          show (codeMat 478 : Mat3).transpose * codeMat 446 * (codeMat 443 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 113 (by decide))
      (by unfold actionA; rw [o435_QtInv_254_443]
          show (codeMat 478 : Mat3).transpose * codeMat 113 * (codeMat 443 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s29_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨29, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s29_actual_le_transport
    (o435_qra_action_code 478 254 (by decide) (by decide) step99_orbit69_lb15_unconditional)

private theorem o435d_s29_qra : QuotientRankAtLeast (o435SourceU ⟨29, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s29_sourceU_le_actual o435d_s29_qra_actual

-- Source 30: orbit69, lb=15, action, P=470, Q=253
private theorem o435d_s30_actual_le_transport :
    o435ActualSourceSpan ⟨30, by omega⟩ ≤
    actionW (codeMat 470) (codeMat 253) o69W := by
  apply o435_spanCodes_le_of_gens [256, 135, 70, 33, 19, 10]
    (actionW (codeMat 470) (codeMat 253) o69W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 27 (by decide))
      (by unfold actionA; rw [o435_QtInv_253_415]
          show (codeMat 470 : Mat3).transpose * codeMat 27 * (codeMat 415 : Mat3).transpose = codeMat 256
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 180 (by decide))
      (by unfold actionA; rw [o435_QtInv_253_415]
          show (codeMat 470 : Mat3).transpose * codeMat 180 * (codeMat 415 : Mat3).transpose = codeMat 135
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 378 (by decide))
      (by unfold actionA; rw [o435_QtInv_253_415]
          show (codeMat 470 : Mat3).transpose * codeMat 378 * (codeMat 415 : Mat3).transpose = codeMat 70
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 479 (by decide))
      (by unfold actionA; rw [o435_QtInv_253_415]
          show (codeMat 470 : Mat3).transpose * codeMat 479 * (codeMat 415 : Mat3).transpose = codeMat 33
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 113 (by decide))
      (by unfold actionA; rw [o435_QtInv_253_415]
          show (codeMat 470 : Mat3).transpose * codeMat 113 * (codeMat 415 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 446 (by decide))
      (by unfold actionA; rw [o435_QtInv_253_415]
          show (codeMat 470 : Mat3).transpose * codeMat 446 * (codeMat 415 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s30_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨30, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s30_actual_le_transport
    (o435_qra_action_code 470 253 (by decide) (by decide) step99_orbit69_lb15_unconditional)

private theorem o435d_s30_qra : QuotientRankAtLeast (o435SourceU ⟨30, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s30_sourceU_le_actual o435d_s30_qra_actual

-- Source 31: orbit69, lb=15, action, P=478, Q=478
private theorem o435d_s31_actual_le_transport :
    o435ActualSourceSpan ⟨31, by omega⟩ ≤
    actionW (codeMat 478) (codeMat 478) o69W := by
  apply o435_spanCodes_le_of_gens [258, 134, 71, 37, 19, 10]
    (actionW (codeMat 478) (codeMat 478) o69W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 175 (by decide))
      (by unfold actionA; rw [o435_QtInv_478_445]
          show (codeMat 478 : Mat3).transpose * codeMat 175 * (codeMat 445 : Mat3).transpose = codeMat 258
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 378 (by decide))
      (by unfold actionA; rw [o435_QtInv_478_445]
          show (codeMat 478 : Mat3).transpose * codeMat 378 * (codeMat 445 : Mat3).transpose = codeMat 134
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 180 (by decide))
      (by unfold actionA; rw [o435_QtInv_478_445]
          show (codeMat 478 : Mat3).transpose * codeMat 180 * (codeMat 445 : Mat3).transpose = codeMat 71
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 430 (by decide))
      (by unfold actionA; rw [o435_QtInv_478_445]
          show (codeMat 478 : Mat3).transpose * codeMat 430 * (codeMat 445 : Mat3).transpose = codeMat 37
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 446 (by decide))
      (by unfold actionA; rw [o435_QtInv_478_445]
          show (codeMat 478 : Mat3).transpose * codeMat 446 * (codeMat 445 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 113 (by decide))
      (by unfold actionA; rw [o435_QtInv_478_445]
          show (codeMat 478 : Mat3).transpose * codeMat 113 * (codeMat 445 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s31_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨31, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s31_actual_le_transport
    (o435_qra_action_code 478 478 (by decide) (by decide) step99_orbit69_lb15_unconditional)

private theorem o435d_s31_qra : QuotientRankAtLeast (o435SourceU ⟨31, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s31_sourceU_le_actual o435d_s31_qra_actual

-- Source 32: orbit69, lb=15, action, P=342, Q=478
private theorem o435d_s32_actual_le_transport :
    o435ActualSourceSpan ⟨32, by omega⟩ ≤
    actionW (codeMat 342) (codeMat 478) o69W := by
  apply o435_spanCodes_le_of_gens [262, 135, 70, 35, 19, 10]
    (actionW (codeMat 342) (codeMat 478) o69W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 191 (by decide))
      (by unfold actionA; rw [o435_QtInv_478_445]
          show (codeMat 342 : Mat3).transpose * codeMat 191 * (codeMat 445 : Mat3).transpose = codeMat 262
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 283 (by decide))
      (by unfold actionA; rw [o435_QtInv_478_445]
          show (codeMat 342 : Mat3).transpose * codeMat 283 * (codeMat 445 : Mat3).transpose = codeMat 135
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 164 (by decide))
      (by unfold actionA; rw [o435_QtInv_478_445]
          show (codeMat 342 : Mat3).transpose * codeMat 164 * (codeMat 445 : Mat3).transpose = codeMat 70
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 97 (by decide))
      (by unfold actionA; rw [o435_QtInv_478_445]
          show (codeMat 342 : Mat3).transpose * codeMat 97 * (codeMat 445 : Mat3).transpose = codeMat 35
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 113 (by decide))
      (by unfold actionA; rw [o435_QtInv_478_445]
          show (codeMat 342 : Mat3).transpose * codeMat 113 * (codeMat 445 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 463 (by decide))
      (by unfold actionA; rw [o435_QtInv_478_445]
          show (codeMat 342 : Mat3).transpose * codeMat 463 * (codeMat 445 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s32_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨32, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s32_actual_le_transport
    (o435_qra_action_code 342 478 (by decide) (by decide) step99_orbit69_lb15_unconditional)

private theorem o435d_s32_qra : QuotientRankAtLeast (o435SourceU ⟨32, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s32_sourceU_le_actual o435d_s32_qra_actual

-- Source 33: orbit69, lb=15, action, P=470, Q=473
private theorem o435d_s33_actual_le_transport :
    o435ActualSourceSpan ⟨33, by omega⟩ ≤
    actionW (codeMat 470) (codeMat 473) o69W := by
  apply o435_spanCodes_le_of_gens [263, 134, 71, 35, 19, 10]
    (actionW (codeMat 470) (codeMat 473) o69W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 353 (by decide))
      (by unfold actionA; rw [o435_QtInv_473_409]
          show (codeMat 470 : Mat3).transpose * codeMat 353 * (codeMat 409 : Mat3).transpose = codeMat 263
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 180 (by decide))
      (by unfold actionA; rw [o435_QtInv_473_409]
          show (codeMat 470 : Mat3).transpose * codeMat 180 * (codeMat 409 : Mat3).transpose = codeMat 134
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 378 (by decide))
      (by unfold actionA; rw [o435_QtInv_473_409]
          show (codeMat 470 : Mat3).transpose * codeMat 378 * (codeMat 409 : Mat3).transpose = codeMat 71
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 97 (by decide))
      (by unfold actionA; rw [o435_QtInv_473_409]
          show (codeMat 470 : Mat3).transpose * codeMat 97 * (codeMat 409 : Mat3).transpose = codeMat 35
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 113 (by decide))
      (by unfold actionA; rw [o435_QtInv_473_409]
          show (codeMat 470 : Mat3).transpose * codeMat 113 * (codeMat 409 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 446 (by decide))
      (by unfold actionA; rw [o435_QtInv_473_409]
          show (codeMat 470 : Mat3).transpose * codeMat 446 * (codeMat 409 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s33_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨33, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s33_actual_le_transport
    (o435_qra_action_code 470 473 (by decide) (by decide) step99_orbit69_lb15_unconditional)

private theorem o435d_s33_qra : QuotientRankAtLeast (o435SourceU ⟨33, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s33_sourceU_le_actual o435d_s33_qra_actual

-- Source 34: orbit69, lb=15, action, P=478, Q=474
private theorem o435d_s34_actual_le_transport :
    o435ActualSourceSpan ⟨34, by omega⟩ ≤
    actionW (codeMat 478) (codeMat 474) o69W := by
  apply o435_spanCodes_le_of_gens [259, 133, 68, 39, 19, 10]
    (actionW (codeMat 478) (codeMat 474) o69W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 353 (by decide))
      (by unfold actionA; rw [o435_QtInv_474_395]
          show (codeMat 478 : Mat3).transpose * codeMat 353 * (codeMat 395 : Mat3).transpose = codeMat 259
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 378 (by decide))
      (by unfold actionA; rw [o435_QtInv_474_395]
          show (codeMat 478 : Mat3).transpose * codeMat 378 * (codeMat 395 : Mat3).transpose = codeMat 133
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 180 (by decide))
      (by unfold actionA; rw [o435_QtInv_474_395]
          show (codeMat 478 : Mat3).transpose * codeMat 180 * (codeMat 395 : Mat3).transpose = codeMat 68
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 97 (by decide))
      (by unfold actionA; rw [o435_QtInv_474_395]
          show (codeMat 478 : Mat3).transpose * codeMat 97 * (codeMat 395 : Mat3).transpose = codeMat 39
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 446 (by decide))
      (by unfold actionA; rw [o435_QtInv_474_395]
          show (codeMat 478 : Mat3).transpose * codeMat 446 * (codeMat 395 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 113 (by decide))
      (by unfold actionA; rw [o435_QtInv_474_395]
          show (codeMat 478 : Mat3).transpose * codeMat 113 * (codeMat 395 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s34_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨34, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s34_actual_le_transport
    (o435_qra_action_code 478 474 (by decide) (by decide) step99_orbit69_lb15_unconditional)

private theorem o435d_s34_qra : QuotientRankAtLeast (o435SourceU ⟨34, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s34_sourceU_le_actual o435d_s34_qra_actual

-- Source 35: orbit69, lb=15, action, P=334, Q=249
private theorem o435d_s35_actual_le_transport :
    o435ActualSourceSpan ⟨35, by omega⟩ ≤
    actionW (codeMat 334) (codeMat 249) o69W := by
  apply o435_spanCodes_le_of_gens [291, 161, 96, 19, 10, 4]
    (actionW (codeMat 334) (codeMat 249) o69W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 10 (by decide))
      (by unfold actionA; rw [o435_QtInv_249_425]
          show (codeMat 334 : Mat3).transpose * codeMat 10 * (codeMat 425 : Mat3).transpose = codeMat 291
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 282 (by decide))
      (by unfold actionA; rw [o435_QtInv_249_425]
          show (codeMat 334 : Mat3).transpose * codeMat 282 * (codeMat 425 : Mat3).transpose = codeMat 161
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 362 (by decide))
      (by unfold actionA; rw [o435_QtInv_249_425]
          show (codeMat 334 : Mat3).transpose * codeMat 362 * (codeMat 425 : Mat3).transpose = codeMat 96
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 446 (by decide))
      (by unfold actionA; rw [o435_QtInv_249_425]
          show (codeMat 334 : Mat3).transpose * codeMat 446 * (codeMat 425 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 463 (by decide))
      (by unfold actionA; rw [o435_QtInv_249_425]
          show (codeMat 334 : Mat3).transpose * codeMat 463 * (codeMat 425 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 16 (by decide))
      (by unfold actionA; rw [o435_QtInv_249_425]
          show (codeMat 334 : Mat3).transpose * codeMat 16 * (codeMat 425 : Mat3).transpose = codeMat 4
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s35_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨35, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s35_actual_le_transport
    (o435_qra_action_code 334 249 (by decide) (by decide) step99_orbit69_lb15_unconditional)

private theorem o435d_s35_qra : QuotientRankAtLeast (o435SourceU ⟨35, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s35_sourceU_le_actual o435d_s35_qra_actual

-- Source 36: orbit69, lb=15, action, P=270, Q=250
private theorem o435d_s36_actual_le_transport :
    o435ActualSourceSpan ⟨36, by omega⟩ ≤
    actionW (codeMat 270) (codeMat 250) o69W := by
  apply o435_spanCodes_le_of_gens [291, 162, 99, 19, 10, 4]
    (actionW (codeMat 270) (codeMat 250) o69W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 10 (by decide))
      (by unfold actionA; rw [o435_QtInv_250_397]
          show (codeMat 270 : Mat3).transpose * codeMat 10 * (codeMat 397 : Mat3).transpose = codeMat 291
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 378 (by decide))
      (by unfold actionA; rw [o435_QtInv_250_397]
          show (codeMat 270 : Mat3).transpose * codeMat 378 * (codeMat 397 : Mat3).transpose = codeMat 162
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 266 (by decide))
      (by unfold actionA; rw [o435_QtInv_250_397]
          show (codeMat 270 : Mat3).transpose * codeMat 266 * (codeMat 397 : Mat3).transpose = codeMat 99
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 463 (by decide))
      (by unfold actionA; rw [o435_QtInv_250_397]
          show (codeMat 270 : Mat3).transpose * codeMat 463 * (codeMat 397 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 446 (by decide))
      (by unfold actionA; rw [o435_QtInv_250_397]
          show (codeMat 270 : Mat3).transpose * codeMat 446 * (codeMat 397 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 16 (by decide))
      (by unfold actionA; rw [o435_QtInv_250_397]
          show (codeMat 270 : Mat3).transpose * codeMat 16 * (codeMat 397 : Mat3).transpose = codeMat 4
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s36_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨36, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s36_actual_le_transport
    (o435_qra_action_code 270 250 (by decide) (by decide) step99_orbit69_lb15_unconditional)

private theorem o435d_s36_qra : QuotientRankAtLeast (o435SourceU ⟨36, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s36_sourceU_le_actual o435d_s36_qra_actual

-- Source 37: orbit69, lb=15, action, P=270, Q=478
private theorem o435d_s37_actual_le_transport :
    o435ActualSourceSpan ⟨37, by omega⟩ ≤
    actionW (codeMat 270) (codeMat 478) o69W := by
  apply o435_spanCodes_le_of_gens [257, 161, 96, 19, 10, 6]
    (actionW (codeMat 270) (codeMat 478) o69W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 368 (by decide))
      (by unfold actionA; rw [o435_QtInv_478_445]
          show (codeMat 270 : Mat3).transpose * codeMat 368 * (codeMat 445 : Mat3).transpose = codeMat 257
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 181 (by decide))
      (by unfold actionA; rw [o435_QtInv_478_445]
          show (codeMat 270 : Mat3).transpose * codeMat 181 * (codeMat 445 : Mat3).transpose = codeMat 161
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 197 (by decide))
      (by unfold actionA; rw [o435_QtInv_478_445]
          show (codeMat 270 : Mat3).transpose * codeMat 197 * (codeMat 445 : Mat3).transpose = codeMat 96
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 463 (by decide))
      (by unfold actionA; rw [o435_QtInv_478_445]
          show (codeMat 270 : Mat3).transpose * codeMat 463 * (codeMat 445 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 446 (by decide))
      (by unfold actionA; rw [o435_QtInv_478_445]
          show (codeMat 270 : Mat3).transpose * codeMat 446 * (codeMat 445 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 16 (by decide))
      (by unfold actionA; rw [o435_QtInv_478_445]
          show (codeMat 270 : Mat3).transpose * codeMat 16 * (codeMat 445 : Mat3).transpose = codeMat 6
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s37_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨37, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s37_actual_le_transport
    (o435_qra_action_code 270 478 (by decide) (by decide) step99_orbit69_lb15_unconditional)

private theorem o435d_s37_qra : QuotientRankAtLeast (o435SourceU ⟨37, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s37_sourceU_le_actual o435d_s37_qra_actual

-- Source 38: orbit69, lb=15, action, P=270, Q=474
private theorem o435d_s38_actual_le_transport :
    o435ActualSourceSpan ⟨38, by omega⟩ ≤
    actionW (codeMat 270) (codeMat 474) o69W := by
  apply o435_spanCodes_le_of_gens [256, 160, 97, 19, 10, 5]
    (actionW (codeMat 270) (codeMat 474) o69W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 256 (by decide))
      (by unfold actionA; rw [o435_QtInv_474_395]
          show (codeMat 270 : Mat3).transpose * codeMat 256 * (codeMat 395 : Mat3).transpose = codeMat 256
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 196 (by decide))
      (by unfold actionA; rw [o435_QtInv_474_395]
          show (codeMat 270 : Mat3).transpose * codeMat 196 * (codeMat 395 : Mat3).transpose = codeMat 160
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 180 (by decide))
      (by unfold actionA; rw [o435_QtInv_474_395]
          show (codeMat 270 : Mat3).transpose * codeMat 180 * (codeMat 395 : Mat3).transpose = codeMat 97
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 463 (by decide))
      (by unfold actionA; rw [o435_QtInv_474_395]
          show (codeMat 270 : Mat3).transpose * codeMat 463 * (codeMat 395 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 446 (by decide))
      (by unfold actionA; rw [o435_QtInv_474_395]
          show (codeMat 270 : Mat3).transpose * codeMat 446 * (codeMat 395 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 16 (by decide))
      (by unfold actionA; rw [o435_QtInv_474_395]
          show (codeMat 270 : Mat3).transpose * codeMat 16 * (codeMat 395 : Mat3).transpose = codeMat 5
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s38_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨38, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s38_actual_le_transport
    (o435_qra_action_code 270 474 (by decide) (by decide) step99_orbit69_lb15_unconditional)

private theorem o435d_s38_qra : QuotientRankAtLeast (o435SourceU ⟨38, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s38_sourceU_le_actual o435d_s38_qra_actual

-- Source 39: orbit69, lb=15, action, P=270, Q=254
private theorem o435d_s39_actual_le_transport :
    o435ActualSourceSpan ⟨39, by omega⟩ ≤
    actionW (codeMat 270) (codeMat 254) o69W := by
  apply o435_spanCodes_le_of_gens [291, 163, 98, 19, 10, 7]
    (actionW (codeMat 270) (codeMat 254) o69W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 11 (by decide))
      (by unfold actionA; rw [o435_QtInv_254_443]
          show (codeMat 270 : Mat3).transpose * codeMat 11 * (codeMat 443 : Mat3).transpose = codeMat 291
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 267 (by decide))
      (by unfold actionA; rw [o435_QtInv_254_443]
          show (codeMat 270 : Mat3).transpose * codeMat 267 * (codeMat 443 : Mat3).transpose = codeMat 163
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 379 (by decide))
      (by unfold actionA; rw [o435_QtInv_254_443]
          show (codeMat 270 : Mat3).transpose * codeMat 379 * (codeMat 443 : Mat3).transpose = codeMat 98
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 463 (by decide))
      (by unfold actionA; rw [o435_QtInv_254_443]
          show (codeMat 270 : Mat3).transpose * codeMat 463 * (codeMat 443 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 446 (by decide))
      (by unfold actionA; rw [o435_QtInv_254_443]
          show (codeMat 270 : Mat3).transpose * codeMat 446 * (codeMat 443 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 16 (by decide))
      (by unfold actionA; rw [o435_QtInv_254_443]
          show (codeMat 270 : Mat3).transpose * codeMat 16 * (codeMat 443 : Mat3).transpose = codeMat 7
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s39_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨39, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s39_actual_le_transport
    (o435_qra_action_code 270 254 (by decide) (by decide) step99_orbit69_lb15_unconditional)

private theorem o435d_s39_qra : QuotientRankAtLeast (o435SourceU ⟨39, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s39_sourceU_le_actual o435d_s39_qra_actual

-- Source 40: orbit69, lb=15, action, P=334, Q=253
private theorem o435d_s40_actual_le_transport :
    o435ActualSourceSpan ⟨40, by omega⟩ ≤
    actionW (codeMat 334) (codeMat 253) o69W := by
  apply o435_spanCodes_le_of_gens [291, 160, 97, 19, 10, 7]
    (actionW (codeMat 334) (codeMat 253) o69W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 11 (by decide))
      (by unfold actionA; rw [o435_QtInv_253_415]
          show (codeMat 334 : Mat3).transpose * codeMat 11 * (codeMat 415 : Mat3).transpose = codeMat 291
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 363 (by decide))
      (by unfold actionA; rw [o435_QtInv_253_415]
          show (codeMat 334 : Mat3).transpose * codeMat 363 * (codeMat 415 : Mat3).transpose = codeMat 160
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 283 (by decide))
      (by unfold actionA; rw [o435_QtInv_253_415]
          show (codeMat 334 : Mat3).transpose * codeMat 283 * (codeMat 415 : Mat3).transpose = codeMat 97
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 446 (by decide))
      (by unfold actionA; rw [o435_QtInv_253_415]
          show (codeMat 334 : Mat3).transpose * codeMat 446 * (codeMat 415 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 463 (by decide))
      (by unfold actionA; rw [o435_QtInv_253_415]
          show (codeMat 334 : Mat3).transpose * codeMat 463 * (codeMat 415 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 16 (by decide))
      (by unfold actionA; rw [o435_QtInv_253_415]
          show (codeMat 334 : Mat3).transpose * codeMat 16 * (codeMat 415 : Mat3).transpose = codeMat 7
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s40_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨40, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s40_actual_le_transport
    (o435_qra_action_code 334 253 (by decide) (by decide) step99_orbit69_lb15_unconditional)

private theorem o435d_s40_qra : QuotientRankAtLeast (o435SourceU ⟨40, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s40_sourceU_le_actual o435d_s40_qra_actual

-- Source 41: orbit31, lb=15, transpose_after_action, P=266, Q=169
private theorem o435d_s41_actual_le_transport :
    o435ActualSourceSpan ⟨41, by omega⟩ ≤
    transposeW (actionW (codeMat 266) (codeMat 169) orbit31W) := by
  apply o435_spanCodes_le_of_gens [261, 128, 65, 17, 8, 2]
    (transposeW (actionW (codeMat 266) (codeMat 169) orbit31W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact ⟨codeMat 321,
      o435_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 88 (by decide))
        (by unfold actionA; rw [o435_QtInv_169_225]
            show (codeMat 266 : Mat3).transpose * codeMat 88 * (codeMat 225 : Mat3).transpose = codeMat 321
            ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h1
    exact ⟨codeMat 32,
      o435_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 2 (by decide))
        (by unfold actionA; rw [o435_QtInv_169_225]
            show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 225 : Mat3).transpose = codeMat 32
            ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h2
    exact ⟨codeMat 5,
      o435_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 8 (by decide))
        (by unfold actionA; rw [o435_QtInv_169_225]
            show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 225 : Mat3).transpose = codeMat 5
            ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h3
    exact ⟨codeMat 17,
      o435_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 28 (by decide))
        (by unfold actionA; rw [o435_QtInv_169_225]
            show (codeMat 266 : Mat3).transpose * codeMat 28 * (codeMat 225 : Mat3).transpose = codeMat 17
            ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h4
    exact ⟨codeMat 2,
      o435_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 32 (by decide))
        (by unfold actionA; rw [o435_QtInv_169_225]
            show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 225 : Mat3).transpose = codeMat 2
            ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h5
    exact ⟨codeMat 8,
      o435_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 3 (by decide))
        (by unfold actionA; rw [o435_QtInv_169_225]
            show (codeMat 266 : Mat3).transpose * codeMat 3 * (codeMat 225 : Mat3).transpose = codeMat 8
            ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩

private theorem o435d_s41_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨41, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s41_actual_le_transport
    (quotientRankAtLeast_transpose (o435_qra_action_code 266 169 (by decide) (by decide) orbit31_lb15))

private theorem o435d_s41_qra : QuotientRankAtLeast (o435SourceU ⟨41, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s41_sourceU_le_actual o435d_s41_qra_actual

-- Source 42: orbit31, lb=15, transpose_after_action, P=266, Q=345
private theorem o435d_s42_actual_le_transport :
    o435ActualSourceSpan ⟨42, by omega⟩ ≤
    transposeW (actionW (codeMat 266) (codeMat 345) orbit31W) := by
  apply o435_spanCodes_le_of_gens [293, 129, 64, 16, 9, 3]
    (transposeW (actionW (codeMat 266) (codeMat 345) orbit31W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact ⟨codeMat 449,
      o435_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 120 (by decide))
        (by unfold actionA; rw [o435_QtInv_345_345]
            show (codeMat 266 : Mat3).transpose * codeMat 120 * (codeMat 345 : Mat3).transpose = codeMat 449
            ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h1
    exact ⟨codeMat 33,
      o435_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 60 (by decide))
        (by unfold actionA; rw [o435_QtInv_345_345]
            show (codeMat 266 : Mat3).transpose * codeMat 60 * (codeMat 345 : Mat3).transpose = codeMat 33
            ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h2
    exact ⟨codeMat 4,
      o435_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 32 (by decide))
        (by unfold actionA; rw [o435_QtInv_345_345]
            show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 345 : Mat3).transpose = codeMat 4
            ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h3
    exact ⟨codeMat 16,
      o435_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 2 (by decide))
        (by unfold actionA; rw [o435_QtInv_345_345]
            show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 345 : Mat3).transpose = codeMat 16
            ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h4
    exact ⟨codeMat 3,
      o435_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 40 (by decide))
        (by unfold actionA; rw [o435_QtInv_345_345]
            show (codeMat 266 : Mat3).transpose * codeMat 40 * (codeMat 345 : Mat3).transpose = codeMat 3
            ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h5
    exact ⟨codeMat 9,
      o435_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 63 (by decide))
        (by unfold actionA; rw [o435_QtInv_345_345]
            show (codeMat 266 : Mat3).transpose * codeMat 63 * (codeMat 345 : Mat3).transpose = codeMat 9
            ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩

private theorem o435d_s42_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨42, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s42_actual_le_transport
    (quotientRankAtLeast_transpose (o435_qra_action_code 266 345 (by decide) (by decide) orbit31_lb15))

private theorem o435d_s42_qra : QuotientRankAtLeast (o435SourceU ⟨42, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s42_sourceU_le_actual o435d_s42_qra_actual

-- Source 43: orbit31, lb=15, transpose_after_action, P=266, Q=212
private theorem o435d_s43_actual_le_transport :
    o435ActualSourceSpan ⟨43, by omega⟩ ≤
    transposeW (actionW (codeMat 266) (codeMat 212) orbit31W) := by
  apply o435_spanCodes_le_of_gens [258, 128, 64, 18, 10, 1]
    (transposeW (actionW (codeMat 266) (codeMat 212) orbit31W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact ⟨codeMat 264,
      o435_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 68 (by decide))
        (by unfold actionA; rw [o435_QtInv_212_86]
            show (codeMat 266 : Mat3).transpose * codeMat 68 * (codeMat 86 : Mat3).transpose = codeMat 264
            ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h1
    exact ⟨codeMat 32,
      o435_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 1 (by decide))
        (by unfold actionA; rw [o435_QtInv_212_86]
            show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 86 : Mat3).transpose = codeMat 32
            ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h2
    exact ⟨codeMat 4,
      o435_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 8 (by decide))
        (by unfold actionA; rw [o435_QtInv_212_86]
            show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 86 : Mat3).transpose = codeMat 4
            ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h3
    exact ⟨codeMat 24,
      o435_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 2 (by decide))
        (by unfold actionA; rw [o435_QtInv_212_86]
            show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 86 : Mat3).transpose = codeMat 24
            ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h4
    exact ⟨codeMat 10,
      o435_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 52 (by decide))
        (by unfold actionA; rw [o435_QtInv_212_86]
            show (codeMat 266 : Mat3).transpose * codeMat 52 * (codeMat 86 : Mat3).transpose = codeMat 10
            ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  · subst h5
    exact ⟨codeMat 1,
      o435_codeMat_mem_actionW_of_witness
        (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 32 (by decide))
        (by unfold actionA; rw [o435_QtInv_212_86]
            show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 86 : Mat3).transpose = codeMat 1
            ext i j <;> fin_cases i <;> fin_cases j <;> decide),
      by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩

private theorem o435d_s43_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨43, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s43_actual_le_transport
    (quotientRankAtLeast_transpose (o435_qra_action_code 266 212 (by decide) (by decide) orbit31_lb15))

private theorem o435d_s43_qra : QuotientRankAtLeast (o435SourceU ⟨43, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s43_sourceU_le_actual o435d_s43_qra_actual

-- Source 44: orbit72, lb=15, action, P=267, Q=409
private theorem o435d_s44_actual_le_transport :
    o435ActualSourceSpan ⟨44, by omega⟩ ≤
    actionW (codeMat 267) (codeMat 409) o72W_wc := by
  apply o435_spanCodes_le_of_gens [259, 193, 34, 19, 10, 4]
    (actionW (codeMat 267) (codeMat 409) o72W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 296 (by decide))
      (by unfold actionA; rw [o435_QtInv_409_473]
          show (codeMat 267 : Mat3).transpose * codeMat 296 * (codeMat 473 : Mat3).transpose = codeMat 259
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 344 (by decide))
      (by unfold actionA; rw [o435_QtInv_409_473]
          show (codeMat 267 : Mat3).transpose * codeMat 344 * (codeMat 473 : Mat3).transpose = codeMat 193
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 20 (by decide))
      (by unfold actionA; rw [o435_QtInv_409_473]
          show (codeMat 267 : Mat3).transpose * codeMat 20 * (codeMat 473 : Mat3).transpose = codeMat 34
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 30 (by decide))
      (by unfold actionA; rw [o435_QtInv_409_473]
          show (codeMat 267 : Mat3).transpose * codeMat 30 * (codeMat 473 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 43 (by decide))
      (by unfold actionA; rw [o435_QtInv_409_473]
          show (codeMat 267 : Mat3).transpose * codeMat 43 * (codeMat 473 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 32 (by decide))
      (by unfold actionA; rw [o435_QtInv_409_473]
          show (codeMat 267 : Mat3).transpose * codeMat 32 * (codeMat 473 : Mat3).transpose = codeMat 4
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s44_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨44, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s44_actual_le_transport
    (o435_qra_action_code 267 409 (by decide) (by decide) step109_orbit72_lb15_wc)

private theorem o435d_s44_qra : QuotientRankAtLeast (o435SourceU ⟨44, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s44_sourceU_le_actual o435d_s44_qra_actual

-- Source 45: orbit72, lb=15, action, P=330, Q=346
private theorem o435d_s45_actual_le_transport :
    o435ActualSourceSpan ⟨45, by omega⟩ ≤
    actionW (codeMat 330) (codeMat 346) o72W_wc := by
  apply o435_spanCodes_le_of_gens [259, 193, 33, 19, 10, 4]
    (actionW (codeMat 330) (codeMat 346) o72W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 264 (by decide))
      (by unfold actionA; rw [o435_QtInv_346_459]
          show (codeMat 330 : Mat3).transpose * codeMat 264 * (codeMat 459 : Mat3).transpose = codeMat 259
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 344 (by decide))
      (by unfold actionA; rw [o435_QtInv_346_459]
          show (codeMat 330 : Mat3).transpose * codeMat 344 * (codeMat 459 : Mat3).transpose = codeMat 193
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 52 (by decide))
      (by unfold actionA; rw [o435_QtInv_346_459]
          show (codeMat 330 : Mat3).transpose * codeMat 52 * (codeMat 459 : Mat3).transpose = codeMat 33
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 43 (by decide))
      (by unfold actionA; rw [o435_QtInv_346_459]
          show (codeMat 330 : Mat3).transpose * codeMat 43 * (codeMat 459 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 30 (by decide))
      (by unfold actionA; rw [o435_QtInv_346_459]
          show (codeMat 330 : Mat3).transpose * codeMat 30 * (codeMat 459 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 32 (by decide))
      (by unfold actionA; rw [o435_QtInv_346_459]
          show (codeMat 330 : Mat3).transpose * codeMat 32 * (codeMat 459 : Mat3).transpose = codeMat 4
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s45_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨45, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s45_actual_le_transport
    (o435_qra_action_code 330 346 (by decide) (by decide) step109_orbit72_lb15_wc)

private theorem o435d_s45_qra : QuotientRankAtLeast (o435SourceU ⟨45, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s45_sourceU_le_actual o435d_s45_qra_actual

-- Source 46: orbit72, lb=15, action, P=467, Q=382
private theorem o435d_s46_actual_le_transport :
    o435ActualSourceSpan ⟨46, by omega⟩ ≤
    actionW (codeMat 467) (codeMat 382) o72W_wc := by
  apply o435_spanCodes_le_of_gens [322, 193, 35, 19, 10, 4]
    (actionW (codeMat 467) (codeMat 382) o72W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 90 (by decide))
      (by unfold actionA; rw [o435_QtInv_382_499]
          show (codeMat 467 : Mat3).transpose * codeMat 90 * (codeMat 499 : Mat3).transpose = codeMat 322
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 371 (by decide))
      (by unfold actionA; rw [o435_QtInv_382_499]
          show (codeMat 467 : Mat3).transpose * codeMat 371 * (codeMat 499 : Mat3).transpose = codeMat 193
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 21 (by decide))
      (by unfold actionA; rw [o435_QtInv_382_499]
          show (codeMat 467 : Mat3).transpose * codeMat 21 * (codeMat 499 : Mat3).transpose = codeMat 35
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 53 (by decide))
      (by unfold actionA; rw [o435_QtInv_382_499]
          show (codeMat 467 : Mat3).transpose * codeMat 53 * (codeMat 499 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 43 (by decide))
      (by unfold actionA; rw [o435_QtInv_382_499]
          show (codeMat 467 : Mat3).transpose * codeMat 43 * (codeMat 499 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 63 (by decide))
      (by unfold actionA; rw [o435_QtInv_382_499]
          show (codeMat 467 : Mat3).transpose * codeMat 63 * (codeMat 499 : Mat3).transpose = codeMat 4
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s46_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨46, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s46_actual_le_transport
    (o435_qra_action_code 467 382 (by decide) (by decide) step109_orbit72_lb15_wc)

private theorem o435d_s46_qra : QuotientRankAtLeast (o435SourceU ⟨46, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s46_sourceU_le_actual o435d_s46_qra_actual

-- Source 47: orbit72, lb=15, action, P=330, Q=382
private theorem o435d_s47_actual_le_transport :
    o435ActualSourceSpan ⟨47, by omega⟩ ≤
    actionW (codeMat 330) (codeMat 382) o72W_wc := by
  apply o435_spanCodes_le_of_gens [322, 193, 34, 19, 10, 6]
    (actionW (codeMat 330) (codeMat 382) o72W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 80 (by decide))
      (by unfold actionA; rw [o435_QtInv_382_499]
          show (codeMat 330 : Mat3).transpose * codeMat 80 * (codeMat 499 : Mat3).transpose = codeMat 322
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 344 (by decide))
      (by unfold actionA; rw [o435_QtInv_382_499]
          show (codeMat 330 : Mat3).transpose * codeMat 344 * (codeMat 499 : Mat3).transpose = codeMat 193
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 31 (by decide))
      (by unfold actionA; rw [o435_QtInv_382_499]
          show (codeMat 330 : Mat3).transpose * codeMat 31 * (codeMat 499 : Mat3).transpose = codeMat 34
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 43 (by decide))
      (by unfold actionA; rw [o435_QtInv_382_499]
          show (codeMat 330 : Mat3).transpose * codeMat 43 * (codeMat 499 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 30 (by decide))
      (by unfold actionA; rw [o435_QtInv_382_499]
          show (codeMat 330 : Mat3).transpose * codeMat 30 * (codeMat 499 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 32 (by decide))
      (by unfold actionA; rw [o435_QtInv_382_499]
          show (codeMat 330 : Mat3).transpose * codeMat 32 * (codeMat 499 : Mat3).transpose = codeMat 6
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s47_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨47, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s47_actual_le_transport
    (o435_qra_action_code 330 382 (by decide) (by decide) step109_orbit72_lb15_wc)

private theorem o435d_s47_qra : QuotientRankAtLeast (o435SourceU ⟨47, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s47_sourceU_le_actual o435d_s47_qra_actual

-- Source 48: orbit72, lb=15, action, P=267, Q=185
private theorem o435d_s48_actual_le_transport :
    o435ActualSourceSpan ⟨48, by omega⟩ ≤
    actionW (codeMat 267) (codeMat 185) o72W_wc := by
  apply o435_spanCodes_le_of_gens [322, 193, 33, 19, 10, 6]
    (actionW (codeMat 267) (codeMat 185) o72W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 112 (by decide))
      (by unfold actionA; rw [o435_QtInv_185_481]
          show (codeMat 267 : Mat3).transpose * codeMat 112 * (codeMat 481 : Mat3).transpose = codeMat 322
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 344 (by decide))
      (by unfold actionA; rw [o435_QtInv_185_481]
          show (codeMat 267 : Mat3).transpose * codeMat 344 * (codeMat 481 : Mat3).transpose = codeMat 193
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 10 (by decide))
      (by unfold actionA; rw [o435_QtInv_185_481]
          show (codeMat 267 : Mat3).transpose * codeMat 10 * (codeMat 481 : Mat3).transpose = codeMat 33
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 30 (by decide))
      (by unfold actionA; rw [o435_QtInv_185_481]
          show (codeMat 267 : Mat3).transpose * codeMat 30 * (codeMat 481 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 43 (by decide))
      (by unfold actionA; rw [o435_QtInv_185_481]
          show (codeMat 267 : Mat3).transpose * codeMat 43 * (codeMat 481 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 32 (by decide))
      (by unfold actionA; rw [o435_QtInv_185_481]
          show (codeMat 267 : Mat3).transpose * codeMat 32 * (codeMat 481 : Mat3).transpose = codeMat 6
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s48_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨48, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s48_actual_le_transport
    (o435_qra_action_code 267 185 (by decide) (by decide) step109_orbit72_lb15_wc)

private theorem o435d_s48_qra : QuotientRankAtLeast (o435SourceU ⟨48, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s48_sourceU_le_actual o435d_s48_qra_actual

-- Source 49: orbit72, lb=15, action, P=267, Q=445
private theorem o435d_s49_actual_le_transport :
    o435ActualSourceSpan ⟨49, by omega⟩ ≤
    actionW (codeMat 267) (codeMat 445) o72W_wc := by
  apply o435_spanCodes_le_of_gens [323, 193, 32, 19, 10, 5]
    (actionW (codeMat 267) (codeMat 445) o72W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 296 (by decide))
      (by unfold actionA; rw [o435_QtInv_445_478]
          show (codeMat 267 : Mat3).transpose * codeMat 296 * (codeMat 478 : Mat3).transpose = codeMat 323
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 344 (by decide))
      (by unfold actionA; rw [o435_QtInv_445_478]
          show (codeMat 267 : Mat3).transpose * codeMat 344 * (codeMat 478 : Mat3).transpose = codeMat 193
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 63 (by decide))
      (by unfold actionA; rw [o435_QtInv_445_478]
          show (codeMat 267 : Mat3).transpose * codeMat 63 * (codeMat 478 : Mat3).transpose = codeMat 32
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 30 (by decide))
      (by unfold actionA; rw [o435_QtInv_445_478]
          show (codeMat 267 : Mat3).transpose * codeMat 30 * (codeMat 478 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 43 (by decide))
      (by unfold actionA; rw [o435_QtInv_445_478]
          show (codeMat 267 : Mat3).transpose * codeMat 43 * (codeMat 478 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 32 (by decide))
      (by unfold actionA; rw [o435_QtInv_445_478]
          show (codeMat 267 : Mat3).transpose * codeMat 32 * (codeMat 478 : Mat3).transpose = codeMat 5
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s49_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨49, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s49_actual_le_transport
    (o435_qra_action_code 267 445 (by decide) (by decide) step109_orbit72_lb15_wc)

private theorem o435d_s49_qra : QuotientRankAtLeast (o435SourceU ⟨49, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s49_sourceU_le_actual o435d_s49_qra_actual

-- Source 50: orbit72, lb=15, action, P=467, Q=94
private theorem o435d_s50_actual_le_transport :
    o435ActualSourceSpan ⟨50, by omega⟩ ≤
    actionW (codeMat 467) (codeMat 94) o72W_wc := by
  apply o435_spanCodes_le_of_gens [258, 193, 33, 19, 10, 5]
    (actionW (codeMat 467) (codeMat 94) o72W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 90 (by decide))
      (by unfold actionA; rw [o435_QtInv_94_500]
          show (codeMat 467 : Mat3).transpose * codeMat 90 * (codeMat 500 : Mat3).transpose = codeMat 258
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 371 (by decide))
      (by unfold actionA; rw [o435_QtInv_94_500]
          show (codeMat 467 : Mat3).transpose * codeMat 371 * (codeMat 500 : Mat3).transpose = codeMat 193
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 62 (by decide))
      (by unfold actionA; rw [o435_QtInv_94_500]
          show (codeMat 467 : Mat3).transpose * codeMat 62 * (codeMat 500 : Mat3).transpose = codeMat 33
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 53 (by decide))
      (by unfold actionA; rw [o435_QtInv_94_500]
          show (codeMat 467 : Mat3).transpose * codeMat 53 * (codeMat 500 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 43 (by decide))
      (by unfold actionA; rw [o435_QtInv_94_500]
          show (codeMat 467 : Mat3).transpose * codeMat 43 * (codeMat 500 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 63 (by decide))
      (by unfold actionA; rw [o435_QtInv_94_500]
          show (codeMat 467 : Mat3).transpose * codeMat 63 * (codeMat 500 : Mat3).transpose = codeMat 5
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s50_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨50, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s50_actual_le_transport
    (o435_qra_action_code 467 94 (by decide) (by decide) step109_orbit72_lb15_wc)

private theorem o435d_s50_qra : QuotientRankAtLeast (o435SourceU ⟨50, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s50_sourceU_le_actual o435d_s50_qra_actual

-- Source 51: orbit72, lb=15, action, P=330, Q=122
private theorem o435d_s51_actual_le_transport :
    o435ActualSourceSpan ⟨51, by omega⟩ ≤
    actionW (codeMat 330) (codeMat 122) o72W_wc := by
  apply o435_spanCodes_le_of_gens [323, 193, 35, 19, 10, 5]
    (actionW (codeMat 330) (codeMat 122) o72W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 264 (by decide))
      (by unfold actionA; rw [o435_QtInv_122_460]
          show (codeMat 330 : Mat3).transpose * codeMat 264 * (codeMat 460 : Mat3).transpose = codeMat 323
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 344 (by decide))
      (by unfold actionA; rw [o435_QtInv_122_460]
          show (codeMat 330 : Mat3).transpose * codeMat 344 * (codeMat 460 : Mat3).transpose = codeMat 193
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 42 (by decide))
      (by unfold actionA; rw [o435_QtInv_122_460]
          show (codeMat 330 : Mat3).transpose * codeMat 42 * (codeMat 460 : Mat3).transpose = codeMat 35
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 43 (by decide))
      (by unfold actionA; rw [o435_QtInv_122_460]
          show (codeMat 330 : Mat3).transpose * codeMat 43 * (codeMat 460 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 30 (by decide))
      (by unfold actionA; rw [o435_QtInv_122_460]
          show (codeMat 330 : Mat3).transpose * codeMat 30 * (codeMat 460 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 32 (by decide))
      (by unfold actionA; rw [o435_QtInv_122_460]
          show (codeMat 330 : Mat3).transpose * codeMat 32 * (codeMat 460 : Mat3).transpose = codeMat 5
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s51_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨51, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s51_actual_le_transport
    (o435_qra_action_code 330 122 (by decide) (by decide) step109_orbit72_lb15_wc)

private theorem o435d_s51_qra : QuotientRankAtLeast (o435SourceU ⟨51, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s51_sourceU_le_actual o435d_s51_qra_actual

-- Source 52: orbit72, lb=15, action, P=330, Q=94
private theorem o435d_s52_actual_le_transport :
    o435ActualSourceSpan ⟨52, by omega⟩ ≤
    actionW (codeMat 330) (codeMat 94) o72W_wc := by
  apply o435_spanCodes_le_of_gens [258, 193, 32, 19, 10, 7]
    (actionW (codeMat 330) (codeMat 94) o72W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 80 (by decide))
      (by unfold actionA; rw [o435_QtInv_94_500]
          show (codeMat 330 : Mat3).transpose * codeMat 80 * (codeMat 500 : Mat3).transpose = codeMat 258
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 344 (by decide))
      (by unfold actionA; rw [o435_QtInv_94_500]
          show (codeMat 330 : Mat3).transpose * codeMat 344 * (codeMat 500 : Mat3).transpose = codeMat 193
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 1 (by decide))
      (by unfold actionA; rw [o435_QtInv_94_500]
          show (codeMat 330 : Mat3).transpose * codeMat 1 * (codeMat 500 : Mat3).transpose = codeMat 32
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 43 (by decide))
      (by unfold actionA; rw [o435_QtInv_94_500]
          show (codeMat 330 : Mat3).transpose * codeMat 43 * (codeMat 500 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 30 (by decide))
      (by unfold actionA; rw [o435_QtInv_94_500]
          show (codeMat 330 : Mat3).transpose * codeMat 30 * (codeMat 500 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 32 (by decide))
      (by unfold actionA; rw [o435_QtInv_94_500]
          show (codeMat 330 : Mat3).transpose * codeMat 32 * (codeMat 500 : Mat3).transpose = codeMat 7
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s52_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨52, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s52_actual_le_transport
    (o435_qra_action_code 330 94 (by decide) (by decide) step109_orbit72_lb15_wc)

private theorem o435d_s52_qra : QuotientRankAtLeast (o435SourceU ⟨52, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s52_sourceU_le_actual o435d_s52_qra_actual

-- Source 53: orbit72, lb=15, action, P=467, Q=122
private theorem o435d_s53_actual_le_transport :
    o435ActualSourceSpan ⟨53, by omega⟩ ≤
    actionW (codeMat 467) (codeMat 122) o72W_wc := by
  apply o435_spanCodes_le_of_gens [323, 193, 34, 19, 10, 7]
    (actionW (codeMat 467) (codeMat 122) o72W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 297 (by decide))
      (by unfold actionA; rw [o435_QtInv_122_460]
          show (codeMat 467 : Mat3).transpose * codeMat 297 * (codeMat 460 : Mat3).transpose = codeMat 323
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 371 (by decide))
      (by unfold actionA; rw [o435_QtInv_122_460]
          show (codeMat 467 : Mat3).transpose * codeMat 371 * (codeMat 460 : Mat3).transpose = codeMat 193
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 11 (by decide))
      (by unfold actionA; rw [o435_QtInv_122_460]
          show (codeMat 467 : Mat3).transpose * codeMat 11 * (codeMat 460 : Mat3).transpose = codeMat 34
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 53 (by decide))
      (by unfold actionA; rw [o435_QtInv_122_460]
          show (codeMat 467 : Mat3).transpose * codeMat 53 * (codeMat 460 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 43 (by decide))
      (by unfold actionA; rw [o435_QtInv_122_460]
          show (codeMat 467 : Mat3).transpose * codeMat 43 * (codeMat 460 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 63 (by decide))
      (by unfold actionA; rw [o435_QtInv_122_460]
          show (codeMat 467 : Mat3).transpose * codeMat 63 * (codeMat 460 : Mat3).transpose = codeMat 7
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s53_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨53, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435d_s53_actual_le_transport
    (o435_qra_action_code 467 122 (by decide) (by decide) step109_orbit72_lb15_wc)

private theorem o435d_s53_qra : QuotientRankAtLeast (o435SourceU ⟨53, by omega⟩) 15 :=
  quotientRankAtLeast_mono o435s53_sourceU_le_actual o435d_s53_qra_actual

-- Source 54: orbit17, lb=14, action, P=94, Q=478
private theorem o435d_s54_actual_le_transport :
    o435ActualSourceSpan ⟨54, by omega⟩ ≤
    actionW (codeMat 94) (codeMat 478) step81o17s4Wspan := by
  apply o435_spanCodes_le_of_gens [259, 130, 67, 32, 19, 10, 6]
    (actionW (codeMat 94) (codeMat 478) step81o17s4Wspan)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 301 (by decide))
      (by unfold actionA; rw [o435_QtInv_478_445]
          show (codeMat 94 : Mat3).transpose * codeMat 301 * (codeMat 445 : Mat3).transpose = codeMat 259
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 63 (by decide))
      (by unfold actionA; rw [o435_QtInv_478_445]
          show (codeMat 94 : Mat3).transpose * codeMat 63 * (codeMat 445 : Mat3).transpose = codeMat 130
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 502 (by decide))
      (by unfold actionA; rw [o435_QtInv_478_445]
          show (codeMat 94 : Mat3).transpose * codeMat 502 * (codeMat 445 : Mat3).transpose = codeMat 67
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 360 (by decide))
      (by unfold actionA; rw [o435_QtInv_478_445]
          show (codeMat 94 : Mat3).transpose * codeMat 360 * (codeMat 445 : Mat3).transpose = codeMat 32
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 440 (by decide))
      (by unfold actionA; rw [o435_QtInv_478_445]
          show (codeMat 94 : Mat3).transpose * codeMat 440 * (codeMat 445 : Mat3).transpose = codeMat 19
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 112 (by decide))
      (by unfold actionA; rw [o435_QtInv_478_445]
          show (codeMat 94 : Mat3).transpose * codeMat 112 * (codeMat 445 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h6
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 128 (by decide))
      (by unfold actionA; rw [o435_QtInv_478_445]
          show (codeMat 94 : Mat3).transpose * codeMat 128 * (codeMat 445 : Mat3).transpose = codeMat 6
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s54_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨54, by omega⟩) 14 :=
  quotientRankAtLeast_mono o435d_s54_actual_le_transport
    (o435_qra_action_code 94 478 (by decide) (by decide) step81o17s4Span_lb)

private theorem o435d_s54_qra : QuotientRankAtLeast (o435SourceU ⟨54, by omega⟩) 14 :=
  quotientRankAtLeast_mono o435s54_sourceU_le_actual o435d_s54_qra_actual

-- Source 55: orbit10, lb=12, action, P=93, Q=236
private theorem o435d_s55_actual_le_transport :
    o435ActualSourceSpan ⟨55, by omega⟩ ≤
    actionW (codeMat 93) (codeMat 236) orbit10W := by
  apply o435_spanCodes_le_of_gens [260, 133, 68, 36, 17, 8, 2]
    (actionW (codeMat 93) (codeMat 236) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 3 (by decide))
      (by unfold actionA; rw [o435_QtInv_236_123]
          show (codeMat 93 : Mat3).transpose * codeMat 3 * (codeMat 123 : Mat3).transpose = codeMat 260
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide))
      (by unfold actionA; rw [o435_QtInv_236_123]
          show (codeMat 93 : Mat3).transpose * codeMat 68 * (codeMat 123 : Mat3).transpose = codeMat 133
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 326 (by decide))
      (by unfold actionA; rw [o435_QtInv_236_123]
          show (codeMat 93 : Mat3).transpose * codeMat 326 * (codeMat 123 : Mat3).transpose = codeMat 68
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide))
      (by unfold actionA; rw [o435_QtInv_236_123]
          show (codeMat 93 : Mat3).transpose * codeMat 24 * (codeMat 123 : Mat3).transpose = codeMat 36
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide))
      (by unfold actionA; rw [o435_QtInv_236_123]
          show (codeMat 93 : Mat3).transpose * codeMat 160 * (codeMat 123 : Mat3).transpose = codeMat 17
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 432 (by decide))
      (by unfold actionA; rw [o435_QtInv_236_123]
          show (codeMat 93 : Mat3).transpose * codeMat 432 * (codeMat 123 : Mat3).transpose = codeMat 8
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h6
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide))
      (by unfold actionA; rw [o435_QtInv_236_123]
          show (codeMat 93 : Mat3).transpose * codeMat 256 * (codeMat 123 : Mat3).transpose = codeMat 2
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s55_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨55, by omega⟩) 12 :=
  quotientRankAtLeast_mono o435d_s55_actual_le_transport
    (o435_qra_action_code 93 236 (by decide) (by decide) orbit10_lb12)

private theorem o435d_s55_qra : QuotientRankAtLeast (o435SourceU ⟨55, by omega⟩) 12 :=
  quotientRankAtLeast_mono o435s55_sourceU_le_actual o435d_s55_qra_actual

-- Source 56: orbit10, lb=12, action, P=93, Q=492
private theorem o435d_s56_actual_le_transport :
    o435ActualSourceSpan ⟨56, by omega⟩ ≤
    actionW (codeMat 93) (codeMat 492) orbit10W := by
  apply o435_spanCodes_le_of_gens [257, 133, 68, 37, 17, 8, 2]
    (actionW (codeMat 93) (codeMat 492) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 71 (by decide))
      (by unfold actionA; rw [o435_QtInv_492_115]
          show (codeMat 93 : Mat3).transpose * codeMat 71 * (codeMat 115 : Mat3).transpose = codeMat 257
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 324 (by decide))
      (by unfold actionA; rw [o435_QtInv_492_115]
          show (codeMat 93 : Mat3).transpose * codeMat 324 * (codeMat 115 : Mat3).transpose = codeMat 133
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 70 (by decide))
      (by unfold actionA; rw [o435_QtInv_492_115]
          show (codeMat 93 : Mat3).transpose * codeMat 70 * (codeMat 115 : Mat3).transpose = codeMat 68
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 440 (by decide))
      (by unfold actionA; rw [o435_QtInv_492_115]
          show (codeMat 93 : Mat3).transpose * codeMat 440 * (codeMat 115 : Mat3).transpose = codeMat 37
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide))
      (by unfold actionA; rw [o435_QtInv_492_115]
          show (codeMat 93 : Mat3).transpose * codeMat 160 * (codeMat 115 : Mat3).transpose = codeMat 17
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 432 (by decide))
      (by unfold actionA; rw [o435_QtInv_492_115]
          show (codeMat 93 : Mat3).transpose * codeMat 432 * (codeMat 115 : Mat3).transpose = codeMat 8
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h6
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide))
      (by unfold actionA; rw [o435_QtInv_492_115]
          show (codeMat 93 : Mat3).transpose * codeMat 256 * (codeMat 115 : Mat3).transpose = codeMat 2
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s56_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨56, by omega⟩) 12 :=
  quotientRankAtLeast_mono o435d_s56_actual_le_transport
    (o435_qra_action_code 93 492 (by decide) (by decide) orbit10_lb12)

private theorem o435d_s56_qra : QuotientRankAtLeast (o435SourceU ⟨56, by omega⟩) 12 :=
  quotientRankAtLeast_mono o435s56_sourceU_le_actual o435d_s56_qra_actual

-- Source 57: orbit10, lb=12, action, P=93, Q=460
private theorem o435d_s57_actual_le_transport :
    o435ActualSourceSpan ⟨57, by omega⟩ ≤
    actionW (codeMat 93) (codeMat 460) orbit10W := by
  apply o435_spanCodes_le_of_gens [256, 132, 69, 37, 17, 8, 2]
    (actionW (codeMat 93) (codeMat 460) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 325 (by decide))
      (by unfold actionA; rw [o435_QtInv_460_122]
          show (codeMat 93 : Mat3).transpose * codeMat 325 * (codeMat 122 : Mat3).transpose = codeMat 256
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide))
      (by unfold actionA; rw [o435_QtInv_460_122]
          show (codeMat 93 : Mat3).transpose * codeMat 68 * (codeMat 122 : Mat3).transpose = codeMat 132
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 326 (by decide))
      (by unfold actionA; rw [o435_QtInv_460_122]
          show (codeMat 93 : Mat3).transpose * codeMat 326 * (codeMat 122 : Mat3).transpose = codeMat 69
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 424 (by decide))
      (by unfold actionA; rw [o435_QtInv_460_122]
          show (codeMat 93 : Mat3).transpose * codeMat 424 * (codeMat 122 : Mat3).transpose = codeMat 37
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide))
      (by unfold actionA; rw [o435_QtInv_460_122]
          show (codeMat 93 : Mat3).transpose * codeMat 160 * (codeMat 122 : Mat3).transpose = codeMat 17
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 432 (by decide))
      (by unfold actionA; rw [o435_QtInv_460_122]
          show (codeMat 93 : Mat3).transpose * codeMat 432 * (codeMat 122 : Mat3).transpose = codeMat 8
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h6
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide))
      (by unfold actionA; rw [o435_QtInv_460_122]
          show (codeMat 93 : Mat3).transpose * codeMat 256 * (codeMat 122 : Mat3).transpose = codeMat 2
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s57_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨57, by omega⟩) 12 :=
  quotientRankAtLeast_mono o435d_s57_actual_le_transport
    (o435_qra_action_code 93 460 (by decide) (by decide) orbit10_lb12)

private theorem o435d_s57_qra : QuotientRankAtLeast (o435SourceU ⟨57, by omega⟩) 12 :=
  quotientRankAtLeast_mono o435s57_sourceU_le_actual o435d_s57_qra_actual

-- Source 58: orbit10, lb=12, action, P=84, Q=212
private theorem o435d_s58_actual_le_transport :
    o435ActualSourceSpan ⟨58, by omega⟩ ≤
    actionW (codeMat 84) (codeMat 212) orbit10W := by
  apply o435_spanCodes_le_of_gens [256, 132, 68, 32, 18, 10, 1]
    (actionW (codeMat 84) (codeMat 212) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide))
      (by unfold actionA; rw [o435_QtInv_212_86]
          show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 86 : Mat3).transpose = codeMat 256
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 70 (by decide))
      (by unfold actionA; rw [o435_QtInv_212_86]
          show (codeMat 84 : Mat3).transpose * codeMat 70 * (codeMat 86 : Mat3).transpose = codeMat 132
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide))
      (by unfold actionA; rw [o435_QtInv_212_86]
          show (codeMat 84 : Mat3).transpose * codeMat 68 * (codeMat 86 : Mat3).transpose = codeMat 68
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide))
      (by unfold actionA; rw [o435_QtInv_212_86]
          show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 86 : Mat3).transpose = codeMat 32
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 432 (by decide))
      (by unfold actionA; rw [o435_QtInv_212_86]
          show (codeMat 84 : Mat3).transpose * codeMat 432 * (codeMat 86 : Mat3).transpose = codeMat 18
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 416 (by decide))
      (by unfold actionA; rw [o435_QtInv_212_86]
          show (codeMat 84 : Mat3).transpose * codeMat 416 * (codeMat 86 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h6
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide))
      (by unfold actionA; rw [o435_QtInv_212_86]
          show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 86 : Mat3).transpose = codeMat 1
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s58_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨58, by omega⟩) 12 :=
  quotientRankAtLeast_mono o435d_s58_actual_le_transport
    (o435_qra_action_code 84 212 (by decide) (by decide) orbit10_lb12)

private theorem o435d_s58_qra : QuotientRankAtLeast (o435SourceU ⟨58, by omega⟩) 12 :=
  quotientRankAtLeast_mono o435s58_sourceU_le_actual o435d_s58_qra_actual

-- Source 59: orbit10, lb=12, action, P=84, Q=244
private theorem o435d_s59_actual_le_transport :
    o435ActualSourceSpan ⟨59, by omega⟩ ≤
    actionW (codeMat 84) (codeMat 244) orbit10W := by
  apply o435_spanCodes_le_of_gens [256, 134, 70, 32, 18, 10, 1]
    (actionW (codeMat 84) (codeMat 244) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 3 (by decide))
      (by unfold actionA; rw [o435_QtInv_244_95]
          show (codeMat 84 : Mat3).transpose * codeMat 3 * (codeMat 95 : Mat3).transpose = codeMat 256
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 326 (by decide))
      (by unfold actionA; rw [o435_QtInv_244_95]
          show (codeMat 84 : Mat3).transpose * codeMat 326 * (codeMat 95 : Mat3).transpose = codeMat 134
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 324 (by decide))
      (by unfold actionA; rw [o435_QtInv_244_95]
          show (codeMat 84 : Mat3).transpose * codeMat 324 * (codeMat 95 : Mat3).transpose = codeMat 70
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide))
      (by unfold actionA; rw [o435_QtInv_244_95]
          show (codeMat 84 : Mat3).transpose * codeMat 24 * (codeMat 95 : Mat3).transpose = codeMat 32
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 432 (by decide))
      (by unfold actionA; rw [o435_QtInv_244_95]
          show (codeMat 84 : Mat3).transpose * codeMat 432 * (codeMat 95 : Mat3).transpose = codeMat 18
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 416 (by decide))
      (by unfold actionA; rw [o435_QtInv_244_95]
          show (codeMat 84 : Mat3).transpose * codeMat 416 * (codeMat 95 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h6
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide))
      (by unfold actionA; rw [o435_QtInv_244_95]
          show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 95 : Mat3).transpose = codeMat 1
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s59_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨59, by omega⟩) 12 :=
  quotientRankAtLeast_mono o435d_s59_actual_le_transport
    (o435_qra_action_code 84 244 (by decide) (by decide) orbit10_lb12)

private theorem o435d_s59_qra : QuotientRankAtLeast (o435SourceU ⟨59, by omega⟩) 12 :=
  quotientRankAtLeast_mono o435s59_sourceU_le_actual o435d_s59_qra_actual

-- Source 60: orbit10, lb=12, action, P=84, Q=468
private theorem o435d_s60_actual_le_transport :
    o435ActualSourceSpan ⟨60, by omega⟩ ≤
    actionW (codeMat 84) (codeMat 468) orbit10W := by
  apply o435_spanCodes_le_of_gens [260, 132, 68, 34, 18, 10, 1]
    (actionW (codeMat 84) (codeMat 468) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 325 (by decide))
      (by unfold actionA; rw [o435_QtInv_468_87]
          show (codeMat 84 : Mat3).transpose * codeMat 325 * (codeMat 87 : Mat3).transpose = codeMat 260
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 326 (by decide))
      (by unfold actionA; rw [o435_QtInv_468_87]
          show (codeMat 84 : Mat3).transpose * codeMat 326 * (codeMat 87 : Mat3).transpose = codeMat 132
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 324 (by decide))
      (by unfold actionA; rw [o435_QtInv_468_87]
          show (codeMat 84 : Mat3).transpose * codeMat 324 * (codeMat 87 : Mat3).transpose = codeMat 68
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 424 (by decide))
      (by unfold actionA; rw [o435_QtInv_468_87]
          show (codeMat 84 : Mat3).transpose * codeMat 424 * (codeMat 87 : Mat3).transpose = codeMat 34
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 432 (by decide))
      (by unfold actionA; rw [o435_QtInv_468_87]
          show (codeMat 84 : Mat3).transpose * codeMat 432 * (codeMat 87 : Mat3).transpose = codeMat 18
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 416 (by decide))
      (by unfold actionA; rw [o435_QtInv_468_87]
          show (codeMat 84 : Mat3).transpose * codeMat 416 * (codeMat 87 : Mat3).transpose = codeMat 10
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h6
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide))
      (by unfold actionA; rw [o435_QtInv_468_87]
          show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 87 : Mat3).transpose = codeMat 1
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s60_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨60, by omega⟩) 12 :=
  quotientRankAtLeast_mono o435d_s60_actual_le_transport
    (o435_qra_action_code 84 468 (by decide) (by decide) orbit10_lb12)

private theorem o435d_s60_qra : QuotientRankAtLeast (o435SourceU ⟨60, by omega⟩) 12 :=
  quotientRankAtLeast_mono o435s60_sourceU_le_actual o435d_s60_qra_actual

-- Source 61: orbit10, lb=12, action, P=142, Q=236
private theorem o435d_s61_actual_le_transport :
    o435ActualSourceSpan ⟨61, by omega⟩ ≤
    actionW (codeMat 142) (codeMat 236) orbit10W := by
  apply o435_spanCodes_le_of_gens [288, 161, 96, 16, 9, 4, 3]
    (actionW (codeMat 142) (codeMat 236) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 3 (by decide))
      (by unfold actionA; rw [o435_QtInv_236_123]
          show (codeMat 142 : Mat3).transpose * codeMat 3 * (codeMat 123 : Mat3).transpose = codeMat 288
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 500 (by decide))
      (by unfold actionA; rw [o435_QtInv_236_123]
          show (codeMat 142 : Mat3).transpose * codeMat 500 * (codeMat 123 : Mat3).transpose = codeMat 161
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 326 (by decide))
      (by unfold actionA; rw [o435_QtInv_236_123]
          show (codeMat 142 : Mat3).transpose * codeMat 326 * (codeMat 123 : Mat3).transpose = codeMat 96
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide))
      (by unfold actionA; rw [o435_QtInv_236_123]
          show (codeMat 142 : Mat3).transpose * codeMat 256 * (codeMat 123 : Mat3).transpose = codeMat 16
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 432 (by decide))
      (by unfold actionA; rw [o435_QtInv_236_123]
          show (codeMat 142 : Mat3).transpose * codeMat 432 * (codeMat 123 : Mat3).transpose = codeMat 9
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide))
      (by unfold actionA; rw [o435_QtInv_236_123]
          show (codeMat 142 : Mat3).transpose * codeMat 24 * (codeMat 123 : Mat3).transpose = codeMat 4
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h6
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide))
      (by unfold actionA; rw [o435_QtInv_236_123]
          show (codeMat 142 : Mat3).transpose * codeMat 16 * (codeMat 123 : Mat3).transpose = codeMat 3
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s61_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨61, by omega⟩) 12 :=
  quotientRankAtLeast_mono o435d_s61_actual_le_transport
    (o435_qra_action_code 142 236 (by decide) (by decide) orbit10_lb12)

private theorem o435d_s61_qra : QuotientRankAtLeast (o435SourceU ⟨61, by omega⟩) 12 :=
  quotientRankAtLeast_mono o435s61_sourceU_le_actual o435d_s61_qra_actual

-- Source 62: orbit10, lb=12, action, P=142, Q=460
private theorem o435d_s62_actual_le_transport :
    o435ActualSourceSpan ⟨62, by omega⟩ ≤
    actionW (codeMat 142) (codeMat 460) orbit10W := by
  apply o435_spanCodes_le_of_gens [256, 160, 97, 16, 9, 5, 3]
    (actionW (codeMat 142) (codeMat 460) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 325 (by decide))
      (by unfold actionA; rw [o435_QtInv_460_122]
          show (codeMat 142 : Mat3).transpose * codeMat 325 * (codeMat 122 : Mat3).transpose = codeMat 256
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h1
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide))
      (by unfold actionA; rw [o435_QtInv_460_122]
          show (codeMat 142 : Mat3).transpose * codeMat 68 * (codeMat 122 : Mat3).transpose = codeMat 160
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h2
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 246 (by decide))
      (by unfold actionA; rw [o435_QtInv_460_122]
          show (codeMat 142 : Mat3).transpose * codeMat 246 * (codeMat 122 : Mat3).transpose = codeMat 97
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h3
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide))
      (by unfold actionA; rw [o435_QtInv_460_122]
          show (codeMat 142 : Mat3).transpose * codeMat 256 * (codeMat 122 : Mat3).transpose = codeMat 16
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h4
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 432 (by decide))
      (by unfold actionA; rw [o435_QtInv_460_122]
          show (codeMat 142 : Mat3).transpose * codeMat 432 * (codeMat 122 : Mat3).transpose = codeMat 9
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h5
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide))
      (by unfold actionA; rw [o435_QtInv_460_122]
          show (codeMat 142 : Mat3).transpose * codeMat 24 * (codeMat 122 : Mat3).transpose = codeMat 5
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)
  · subst h6
    exact o435_codeMat_mem_actionW_of_witness
      (spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide))
      (by unfold actionA; rw [o435_QtInv_460_122]
          show (codeMat 142 : Mat3).transpose * codeMat 16 * (codeMat 122 : Mat3).transpose = codeMat 3
          ext i j <;> fin_cases i <;> fin_cases j <;> decide)

private theorem o435d_s62_qra_actual : QuotientRankAtLeast (o435ActualSourceSpan ⟨62, by omega⟩) 12 :=
  quotientRankAtLeast_mono o435d_s62_actual_le_transport
    (o435_qra_action_code 142 460 (by decide) (by decide) orbit10_lb12)

private theorem o435d_s62_qra : QuotientRankAtLeast (o435SourceU ⟨62, by omega⟩) 12 :=
  quotientRankAtLeast_mono o435s62_sourceU_le_actual o435d_s62_qra_actual

theorem o435_dispatch_hSource :
    ∀ i : Fin 63, QuotientRankAtLeast (o435SourceU i) (o435SourceLb i) := by
  intro i
  fin_cases i
  · exact o435d_s0_qra
  · exact o435d_s1_qra
  · exact o435d_s2_qra
  · exact o435d_s3_qra
  · exact o435d_s4_qra
  · exact o435d_s5_qra
  · exact o435d_s6_qra
  · exact o435d_s7_qra
  · exact o435d_s8_qra
  · exact o435d_s9_qra
  · exact o435d_s10_qra
  · exact o435d_s11_qra
  · exact o435d_s12_qra
  · exact o435d_s13_qra
  · exact o435d_s14_qra
  · exact o435d_s15_qra
  · exact o435d_s16_qra
  · exact o435d_s17_qra
  · exact o435d_s18_qra
  · exact o435d_s19_qra
  · exact o435d_s20_qra
  · exact o435d_s21_qra
  · exact o435d_s22_qra
  · exact o435d_s23_qra
  · exact o435d_s24_qra
  · exact o435d_s25_qra
  · exact o435d_s26_qra
  · exact o435d_s27_qra
  · exact o435d_s28_qra
  · exact o435d_s29_qra
  · exact o435d_s30_qra
  · exact o435d_s31_qra
  · exact o435d_s32_qra
  · exact o435d_s33_qra
  · exact o435d_s34_qra
  · exact o435d_s35_qra
  · exact o435d_s36_qra
  · exact o435d_s37_qra
  · exact o435d_s38_qra
  · exact o435d_s39_qra
  · exact o435d_s40_qra
  · exact o435d_s41_qra
  · exact o435d_s42_qra
  · exact o435d_s43_qra
  · exact o435d_s44_qra
  · exact o435d_s45_qra
  · exact o435d_s46_qra
  · exact o435d_s47_qra
  · exact o435d_s48_qra
  · exact o435d_s49_qra
  · exact o435d_s50_qra
  · exact o435d_s51_qra
  · exact o435d_s52_qra
  · exact o435d_s53_qra
  · exact o435d_s54_qra
  · exact o435d_s55_qra
  · exact o435d_s56_qra
  · exact o435d_s57_qra
  · exact o435d_s58_qra
  · exact o435d_s59_qra
  · exact o435d_s60_qra
  · exact o435d_s61_qra
  · exact o435d_s62_qra

theorem step136_orbit435_lb17 : QuotientRankAtLeast o435W 17 :=
  o435ScalarLb17 o435_dispatch_hSource

end QiushiMatmul
end
