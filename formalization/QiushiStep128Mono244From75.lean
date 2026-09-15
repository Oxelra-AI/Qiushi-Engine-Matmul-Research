import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit75Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

def o244W_mono : Submodule F2 Mat3 := spanCodes [133, 68, 35, 20, 10]

private theorem o244from75_QtInv :
    (codeMat 234 : Mat3).transpose⁻¹ = (codeMat 461 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 234 : Mat3).transpose * (codeMat 461 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o244W_le_action_75 :
    o244W_mono ≤ actionW (codeMat 93) (codeMat 234) o75W_wc := by
  unfold o244W_mono
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 69 ∈ o75W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 160, 68, 20, 10, 1] 69 (by decide)
    have hact : actionA (codeMat 93) (codeMat 234) (codeMat 69) = codeMat 133 := by
      unfold actionA; rw [o244from75_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 69 * (codeMat 461 : Mat3).transpose = codeMat 133
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o75W_wc ∧ actionA (codeMat 93) (codeMat 234) X = codeMat 133
    exact ⟨codeMat 69, hw, hact⟩
  · subst h1
    have hw : codeMat 262 ∈ o75W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 160, 68, 20, 10, 1] 262 (by decide)
    have hact : actionA (codeMat 93) (codeMat 234) (codeMat 262) = codeMat 68 := by
      unfold actionA; rw [o244from75_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 262 * (codeMat 461 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o75W_wc ∧ actionA (codeMat 93) (codeMat 234) X = codeMat 68
    exact ⟨codeMat 262, hw, hact⟩
  · subst h2
    have hw : codeMat 80 ∈ o75W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 160, 68, 20, 10, 1] 80 (by decide)
    have hact : actionA (codeMat 93) (codeMat 234) (codeMat 80) = codeMat 35 := by
      unfold actionA; rw [o244from75_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 80 * (codeMat 461 : Mat3).transpose = codeMat 35
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o75W_wc ∧ actionA (codeMat 93) (codeMat 234) X = codeMat 35
    exact ⟨codeMat 80, hw, hact⟩
  · subst h3
    have hw : codeMat 488 ∈ o75W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 160, 68, 20, 10, 1] 488 (by decide)
    have hact : actionA (codeMat 93) (codeMat 234) (codeMat 488) = codeMat 20 := by
      unfold actionA; rw [o244from75_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 488 * (codeMat 461 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o75W_wc ∧ actionA (codeMat 93) (codeMat 234) X = codeMat 20
    exact ⟨codeMat 488, hw, hact⟩
  · subst h4
    have hw : codeMat 240 ∈ o75W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 160, 68, 20, 10, 1] 240 (by decide)
    have hact : actionA (codeMat 93) (codeMat 234) (codeMat 240) = codeMat 10 := by
      unfold actionA; rw [o244from75_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 240 * (codeMat 461 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o75W_wc ∧ actionA (codeMat 93) (codeMat 234) X = codeMat 10
    exact ⟨codeMat 240, hw, hact⟩

theorem orbit244_lb16_mono : QuotientRankAtLeast o244W_mono 16 := by
  have hP : Invertible (codeMat 93 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 234 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 93) (codeMat 234) o75W_wc) 16 :=
    @quotientRankAtLeast_action (codeMat 93) (codeMat 234) hP hQ o75W_wc 16
      step109_orbit75_lb16_wc
  exact quotientRankAtLeast_mono o244W_le_action_75 hAct

end QiushiMatmul
