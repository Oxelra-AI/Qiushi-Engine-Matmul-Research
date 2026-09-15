import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiWcOrbit214Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private def o214W_T : Submodule F2 Mat3 := spanCodes [306, 132, 96, 10, 1]

private theorem o214W_T_lb : QuotientRankAtLeast o214W_T 16 := by
  have ht := quotientRankAtLeast_transpose step109_orbit214_lb16_wc
  have hle : o214W_T ≤ transposeW o214W_wc := by
    unfold o214W_T transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4
    · subst h0
      show codeMat 306 ∈ Submodule.map transposeLinearMap o214W_wc
      exact ⟨codeMat 408, spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 408 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 132 ∈ Submodule.map transposeLinearMap o214W_wc
      exact ⟨codeMat 96, spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 96 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 96 ∈ Submodule.map transposeLinearMap o214W_wc
      exact ⟨codeMat 132, spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 132 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 10 ∈ Submodule.map transposeLinearMap o214W_wc
      exact ⟨codeMat 10, spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 10 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 1 ∈ Submodule.map transposeLinearMap o214W_wc
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

def o346W_mono : Submodule F2 Mat3 := spanCodes [424, 100, 16, 1]

private theorem o346from214_QtInv :
    (codeMat 110 : Mat3).transpose⁻¹ = (codeMat 444 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 110 : Mat3).transpose * (codeMat 444 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o346W_le_action_214 :
    o346W_mono ≤ actionW (codeMat 314) (codeMat 110) o214W_T := by
  unfold o346W_mono
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    have hw : codeMat 133 ∈ o214W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 132, 96, 10, 1] 133 (by decide)
    have hact : actionA (codeMat 314) (codeMat 110) (codeMat 133) = codeMat 424 := by
      unfold actionA; rw [o346from214_QtInv]
      show (codeMat 314 : Mat3).transpose * codeMat 133 * (codeMat 444 : Mat3).transpose = codeMat 424
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o214W_T ∧ actionA (codeMat 314) (codeMat 110) X = codeMat 424
    exact ⟨codeMat 133, hw, hact⟩
  · subst h1
    have hw : codeMat 344 ∈ o214W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 132, 96, 10, 1] 344 (by decide)
    have hact : actionA (codeMat 314) (codeMat 110) (codeMat 344) = codeMat 100 := by
      unfold actionA; rw [o346from214_QtInv]
      show (codeMat 314 : Mat3).transpose * codeMat 344 * (codeMat 444 : Mat3).transpose = codeMat 100
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o214W_T ∧ actionA (codeMat 314) (codeMat 110) X = codeMat 100
    exact ⟨codeMat 344, hw, hact⟩
  · subst h2
    have hw : codeMat 1 ∈ o214W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 132, 96, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 314) (codeMat 110) (codeMat 1) = codeMat 16 := by
      unfold actionA; rw [o346from214_QtInv]
      show (codeMat 314 : Mat3).transpose * codeMat 1 * (codeMat 444 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o214W_T ∧ actionA (codeMat 314) (codeMat 110) X = codeMat 16
    exact ⟨codeMat 1, hw, hact⟩
  · subst h3
    have hw : codeMat 438 ∈ o214W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 132, 96, 10, 1] 438 (by decide)
    have hact : actionA (codeMat 314) (codeMat 110) (codeMat 438) = codeMat 1 := by
      unfold actionA; rw [o346from214_QtInv]
      show (codeMat 314 : Mat3).transpose * codeMat 438 * (codeMat 444 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o214W_T ∧ actionA (codeMat 314) (codeMat 110) X = codeMat 1
    exact ⟨codeMat 438, hw, hact⟩

theorem orbit346_lb16_mono : QuotientRankAtLeast o346W_mono 16 := by
  have hP : Invertible (codeMat 314 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 110 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 314) (codeMat 110) o214W_T) 16 :=
    @quotientRankAtLeast_action (codeMat 314) (codeMat 110) hP hQ o214W_T 16
      o214W_T_lb
  exact quotientRankAtLeast_mono o346W_le_action_214 hAct

end QiushiMatmul
