import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiBranch262Extraction

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private def o262W_T : Submodule F2 Mat3 := spanCodes [66, 34, 8, 1]

private theorem o262W_T_lb : QuotientRankAtLeast o262W_T 17 := by
  have ht := quotientRankAtLeast_transpose step113_orbit262_lb17
  have hle : o262W_T ≤ transposeW o262W := by
    unfold o262W_T transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3
    · subst h0
      show codeMat 66 ∈ Submodule.map transposeLinearMap o262W
      exact ⟨codeMat 12, spanContainsCodeCore_implies_mem_spanCodes [132, 12, 2, 1] 12 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 34 ∈ Submodule.map transposeLinearMap o262W
      exact ⟨codeMat 136, spanContainsCodeCore_implies_mem_spanCodes [132, 12, 2, 1] 136 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 8 ∈ Submodule.map transposeLinearMap o262W
      exact ⟨codeMat 2, spanContainsCodeCore_implies_mem_spanCodes [132, 12, 2, 1] 2 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 1 ∈ Submodule.map transposeLinearMap o262W
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [132, 12, 2, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

def o437W_mono : Submodule F2 Mat3 := spanCodes [100, 20, 1]

private theorem o437from262_QtInv :
    (codeMat 177 : Mat3).transpose⁻¹ = (codeMat 417 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 177 : Mat3).transpose * (codeMat 417 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o437W_le_action_262 :
    o437W_mono ≤ actionW (codeMat 275) (codeMat 177) o262W_T := by
  unfold o437W_mono
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    have hw : codeMat 66 ∈ o262W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [66, 34, 8, 1] 66 (by decide)
    have hact : actionA (codeMat 275) (codeMat 177) (codeMat 66) = codeMat 100 := by
      unfold actionA; rw [o437from262_QtInv]
      show (codeMat 275 : Mat3).transpose * codeMat 66 * (codeMat 417 : Mat3).transpose = codeMat 100
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o262W_T ∧ actionA (codeMat 275) (codeMat 177) X = codeMat 100
    exact ⟨codeMat 66, hw, hact⟩
  · subst h1
    have hw : codeMat 34 ∈ o262W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [66, 34, 8, 1] 34 (by decide)
    have hact : actionA (codeMat 275) (codeMat 177) (codeMat 34) = codeMat 20 := by
      unfold actionA; rw [o437from262_QtInv]
      show (codeMat 275 : Mat3).transpose * codeMat 34 * (codeMat 417 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o262W_T ∧ actionA (codeMat 275) (codeMat 177) X = codeMat 20
    exact ⟨codeMat 34, hw, hact⟩
  · subst h2
    have hw : codeMat 9 ∈ o262W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [66, 34, 8, 1] 9 (by decide)
    have hact : actionA (codeMat 275) (codeMat 177) (codeMat 9) = codeMat 1 := by
      unfold actionA; rw [o437from262_QtInv]
      show (codeMat 275 : Mat3).transpose * codeMat 9 * (codeMat 417 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o262W_T ∧ actionA (codeMat 275) (codeMat 177) X = codeMat 1
    exact ⟨codeMat 9, hw, hact⟩

theorem orbit437_lb17_mono : QuotientRankAtLeast o437W_mono 17 := by
  have hP : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 275) (codeMat 177) o262W_T) 17 :=
    @quotientRankAtLeast_action (codeMat 275) (codeMat 177) hP hQ o262W_T 17
      o262W_T_lb
  exact quotientRankAtLeast_mono o437W_le_action_262 hAct

end QiushiMatmul
