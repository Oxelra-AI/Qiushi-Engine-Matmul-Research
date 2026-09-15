import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit78Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

def o215W_mono : Submodule F2 Mat3 := spanCodes [292, 132, 96, 10, 1]

private theorem o215from78_QtInv :
    (codeMat 489 : Mat3).transpose⁻¹ = (codeMat 241 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 489 : Mat3).transpose * (codeMat 241 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o215W_le_action_78 :
    o215W_mono ≤ actionW (codeMat 157) (codeMat 489) o78W_wc := by
  unfold o215W_mono
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 390 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 390 (by decide)
    have hact : actionA (codeMat 157) (codeMat 489) (codeMat 390) = codeMat 292 := by
      unfold actionA; rw [o215from78_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 390 * (codeMat 241 : Mat3).transpose = codeMat 292
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o78W_wc ∧ actionA (codeMat 157) (codeMat 489) X = codeMat 292
    exact ⟨codeMat 390, hw, hact⟩
  · subst h1
    have hw : codeMat 148 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 148 (by decide)
    have hact : actionA (codeMat 157) (codeMat 489) (codeMat 148) = codeMat 132 := by
      unfold actionA; rw [o215from78_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 148 * (codeMat 241 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o78W_wc ∧ actionA (codeMat 157) (codeMat 489) X = codeMat 132
    exact ⟨codeMat 148, hw, hact⟩
  · subst h2
    have hw : codeMat 127 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 127 (by decide)
    have hact : actionA (codeMat 157) (codeMat 489) (codeMat 127) = codeMat 96 := by
      unfold actionA; rw [o215from78_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 127 * (codeMat 241 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o78W_wc ∧ actionA (codeMat 157) (codeMat 489) X = codeMat 96
    exact ⟨codeMat 127, hw, hact⟩
  · subst h3
    have hw : codeMat 224 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 224 (by decide)
    have hact : actionA (codeMat 157) (codeMat 489) (codeMat 224) = codeMat 10 := by
      unfold actionA; rw [o215from78_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 224 * (codeMat 241 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o78W_wc ∧ actionA (codeMat 157) (codeMat 489) X = codeMat 10
    exact ⟨codeMat 224, hw, hact⟩
  · subst h4
    have hw : codeMat 504 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 504 (by decide)
    have hact : actionA (codeMat 157) (codeMat 489) (codeMat 504) = codeMat 1 := by
      unfold actionA; rw [o215from78_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 504 * (codeMat 241 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o78W_wc ∧ actionA (codeMat 157) (codeMat 489) X = codeMat 1
    exact ⟨codeMat 504, hw, hact⟩

theorem orbit215_lb14_mono : QuotientRankAtLeast o215W_mono 14 := by
  have hP : Invertible (codeMat 157 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 489 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 157) (codeMat 489) o78W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 157) (codeMat 489) hP hQ o78W_wc 14
      step109_orbit78_lb14_wc
  exact quotientRankAtLeast_mono o215W_le_action_78 hAct

end QiushiMatmul
