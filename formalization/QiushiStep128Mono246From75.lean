import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit75Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

def o246W_mono : Submodule F2 Mat3 := spanCodes [259, 162, 68, 20, 10]

private theorem o246from75_QtInv :
    (codeMat 421 : Mat3).transpose⁻¹ = (codeMat 179 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 421 : Mat3).transpose * (codeMat 179 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o246W_le_action_75 :
    o246W_mono ≤ actionW (codeMat 177) (codeMat 421) o75W_wc := by
  unfold o246W_mono
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 509 ∈ o75W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 160, 68, 20, 10, 1] 509 (by decide)
    have hact : actionA (codeMat 177) (codeMat 421) (codeMat 509) = codeMat 259 := by
      unfold actionA; rw [o246from75_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 509 * (codeMat 179 : Mat3).transpose = codeMat 259
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o75W_wc ∧ actionA (codeMat 177) (codeMat 421) X = codeMat 259
    exact ⟨codeMat 509, hw, hact⟩
  · subst h1
    have hw : codeMat 228 ∈ o75W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 160, 68, 20, 10, 1] 228 (by decide)
    have hact : actionA (codeMat 177) (codeMat 421) (codeMat 228) = codeMat 162 := by
      unfold actionA; rw [o246from75_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 228 * (codeMat 179 : Mat3).transpose = codeMat 162
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o75W_wc ∧ actionA (codeMat 177) (codeMat 421) X = codeMat 162
    exact ⟨codeMat 228, hw, hact⟩
  · subst h2
    have hw : codeMat 79 ∈ o75W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 160, 68, 20, 10, 1] 79 (by decide)
    have hact : actionA (codeMat 177) (codeMat 421) (codeMat 79) = codeMat 68 := by
      unfold actionA; rw [o246from75_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 79 * (codeMat 179 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o75W_wc ∧ actionA (codeMat 177) (codeMat 421) X = codeMat 68
    exact ⟨codeMat 79, hw, hact⟩
  · subst h3
    have hw : codeMat 263 ∈ o75W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 160, 68, 20, 10, 1] 263 (by decide)
    have hact : actionA (codeMat 177) (codeMat 421) (codeMat 263) = codeMat 20 := by
      unfold actionA; rw [o246from75_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 263 * (codeMat 179 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o75W_wc ∧ actionA (codeMat 177) (codeMat 421) X = codeMat 20
    exact ⟨codeMat 263, hw, hact⟩
  · subst h4
    have hw : codeMat 68 ∈ o75W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 160, 68, 20, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 177) (codeMat 421) (codeMat 68) = codeMat 10 := by
      unfold actionA; rw [o246from75_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 68 * (codeMat 179 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o75W_wc ∧ actionA (codeMat 177) (codeMat 421) X = codeMat 10
    exact ⟨codeMat 68, hw, hact⟩

theorem orbit246_lb16_mono : QuotientRankAtLeast o246W_mono 16 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 421 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 421) o75W_wc) 16 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 421) hP hQ o75W_wc 16
      step109_orbit75_lb16_wc
  exact quotientRankAtLeast_mono o246W_le_action_75 hAct

end QiushiMatmul
