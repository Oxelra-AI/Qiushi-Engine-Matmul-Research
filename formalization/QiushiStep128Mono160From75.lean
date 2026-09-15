import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit75Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

def o160W_mono : Submodule F2 Mat3 := spanCodes [258, 68, 20, 10, 1]

private theorem o160from75_QtInv :
    (codeMat 163 : Mat3).transpose⁻¹ = (codeMat 165 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 163 : Mat3).transpose * (codeMat 165 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o160W_le_action_75 :
    o160W_mono ≤ actionW (codeMat 161) (codeMat 163) o75W_wc := by
  unfold o160W_mono
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 21 ∈ o75W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 160, 68, 20, 10, 1] 21 (by decide)
    have hact : actionA (codeMat 161) (codeMat 163) (codeMat 21) = codeMat 258 := by
      unfold actionA; rw [o160from75_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 21 * (codeMat 165 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o75W_wc ∧ actionA (codeMat 161) (codeMat 163) X = codeMat 258
    exact ⟨codeMat 21, hw, hact⟩
  · subst h1
    have hw : codeMat 10 ∈ o75W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 160, 68, 20, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 161) (codeMat 163) (codeMat 10) = codeMat 68 := by
      unfold actionA; rw [o160from75_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 10 * (codeMat 165 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o75W_wc ∧ actionA (codeMat 161) (codeMat 163) X = codeMat 68
    exact ⟨codeMat 10, hw, hact⟩
  · subst h2
    have hw : codeMat 322 ∈ o75W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 160, 68, 20, 10, 1] 322 (by decide)
    have hact : actionA (codeMat 161) (codeMat 163) (codeMat 322) = codeMat 20 := by
      unfold actionA; rw [o160from75_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 322 * (codeMat 165 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o75W_wc ∧ actionA (codeMat 161) (codeMat 163) X = codeMat 20
    exact ⟨codeMat 322, hw, hact⟩
  · subst h3
    have hw : codeMat 69 ∈ o75W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 160, 68, 20, 10, 1] 69 (by decide)
    have hact : actionA (codeMat 161) (codeMat 163) (codeMat 69) = codeMat 10 := by
      unfold actionA; rw [o160from75_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 69 * (codeMat 165 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o75W_wc ∧ actionA (codeMat 161) (codeMat 163) X = codeMat 10
    exact ⟨codeMat 69, hw, hact⟩
  · subst h4
    have hw : codeMat 1 ∈ o75W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 160, 68, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 163) (codeMat 1) = codeMat 1 := by
      unfold actionA; rw [o160from75_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 165 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o75W_wc ∧ actionA (codeMat 161) (codeMat 163) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩

theorem orbit160_lb16_mono : QuotientRankAtLeast o160W_mono 16 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 163 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 163) o75W_wc) 16 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 163) hP hQ o75W_wc 16
      step109_orbit75_lb16_wc
  exact quotientRankAtLeast_mono o160W_le_action_75 hAct

end QiushiMatmul
