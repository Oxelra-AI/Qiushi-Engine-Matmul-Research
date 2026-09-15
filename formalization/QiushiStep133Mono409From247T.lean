import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiStep128Mono247From85

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private def o247W_T : Submodule F2 Mat3 := spanCodes [259, 132, 80, 51, 10]

private theorem o247W_T_lb : QuotientRankAtLeast o247W_T 17 := by
  have ht := quotientRankAtLeast_transpose orbit247_lb17_mono
  have hle : o247W_T ≤ transposeW o247W_mono := by
    unfold o247W_T transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4
    · subst h0
      show codeMat 259 ∈ Submodule.map transposeLinearMap o247W_mono
      exact ⟨codeMat 265, spanContainsCodeCore_implies_mem_spanCodes [259, 135, 96, 20, 10] 265 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 132 ∈ Submodule.map transposeLinearMap o247W_mono
      exact ⟨codeMat 96, spanContainsCodeCore_implies_mem_spanCodes [259, 135, 96, 20, 10] 96 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 80 ∈ Submodule.map transposeLinearMap o247W_mono
      exact ⟨codeMat 20, spanContainsCodeCore_implies_mem_spanCodes [259, 135, 96, 20, 10] 20 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 51 ∈ Submodule.map transposeLinearMap o247W_mono
      exact ⟨codeMat 153, spanContainsCodeCore_implies_mem_spanCodes [259, 135, 96, 20, 10] 153 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 10 ∈ Submodule.map transposeLinearMap o247W_mono
      exact ⟨codeMat 10, spanContainsCodeCore_implies_mem_spanCodes [259, 135, 96, 20, 10] 10 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

def o409W_mono : Submodule F2 Mat3 := spanCodes [276, 165, 96, 10]

private theorem o409from247_QtInv :
    (codeMat 98 : Mat3).transpose⁻¹ = (codeMat 140 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 98 : Mat3).transpose * (codeMat 140 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o409W_le_action_247 :
    o409W_mono ≤ actionW (codeMat 94) (codeMat 98) o247W_T := by
  unfold o409W_mono
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    have hw : codeMat 90 ∈ o247W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [259, 132, 80, 51, 10] 90 (by decide)
    have hact : actionA (codeMat 94) (codeMat 98) (codeMat 90) = codeMat 276 := by
      unfold actionA; rw [o409from247_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 90 * (codeMat 140 : Mat3).transpose = codeMat 276
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o247W_T ∧ actionA (codeMat 94) (codeMat 98) X = codeMat 276
    exact ⟨codeMat 90, hw, hact⟩
  · subst h1
    have hw : codeMat 345 ∈ o247W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [259, 132, 80, 51, 10] 345 (by decide)
    have hact : actionA (codeMat 94) (codeMat 98) (codeMat 345) = codeMat 165 := by
      unfold actionA; rw [o409from247_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 345 * (codeMat 140 : Mat3).transpose = codeMat 165
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o247W_T ∧ actionA (codeMat 94) (codeMat 98) X = codeMat 165
    exact ⟨codeMat 345, hw, hact⟩
  · subst h2
    have hw : codeMat 436 ∈ o247W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [259, 132, 80, 51, 10] 436 (by decide)
    have hact : actionA (codeMat 94) (codeMat 98) (codeMat 436) = codeMat 96 := by
      unfold actionA; rw [o409from247_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 436 * (codeMat 140 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o247W_T ∧ actionA (codeMat 94) (codeMat 98) X = codeMat 96
    exact ⟨codeMat 436, hw, hact⟩
  · subst h3
    have hw : codeMat 352 ∈ o247W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [259, 132, 80, 51, 10] 352 (by decide)
    have hact : actionA (codeMat 94) (codeMat 98) (codeMat 352) = codeMat 10 := by
      unfold actionA; rw [o409from247_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 352 * (codeMat 140 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o247W_T ∧ actionA (codeMat 94) (codeMat 98) X = codeMat 10
    exact ⟨codeMat 352, hw, hact⟩

theorem orbit409_lb17_mono : QuotientRankAtLeast o409W_mono 17 := by
  have hP : Invertible (codeMat 94 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 94) (codeMat 98) o247W_T) 17 :=
    @quotientRankAtLeast_action (codeMat 94) (codeMat 98) hP hQ o247W_T 17
      o247W_T_lb
  exact quotientRankAtLeast_mono o409W_le_action_247 hAct

end QiushiMatmul
