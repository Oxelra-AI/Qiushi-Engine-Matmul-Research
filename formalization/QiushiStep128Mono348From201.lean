import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit201Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

def o348W_mono : Submodule F2 Mat3 := spanCodes [262, 228, 16, 1]

private theorem o348from201_QtInv :
    (codeMat 358 : Mat3).transpose⁻¹ = (codeMat 158 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 358 : Mat3).transpose * (codeMat 158 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o348W_le_action_201 :
    o348W_mono ≤ actionW (codeMat 266) (codeMat 358) o201W_wc := by
  unfold o348W_mono
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    have hw : codeMat 496 ∈ o201W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [340, 132, 32, 10, 1] 496 (by decide)
    have hact : actionA (codeMat 266) (codeMat 358) (codeMat 496) = codeMat 262 := by
      unfold actionA; rw [o348from201_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 496 * (codeMat 158 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o201W_wc ∧ actionA (codeMat 266) (codeMat 358) X = codeMat 262
    exact ⟨codeMat 496, hw, hact⟩
  · subst h1
    have hw : codeMat 383 ∈ o201W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [340, 132, 32, 10, 1] 383 (by decide)
    have hact : actionA (codeMat 266) (codeMat 358) (codeMat 383) = codeMat 228 := by
      unfold actionA; rw [o348from201_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 383 * (codeMat 158 : Mat3).transpose = codeMat 228
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o201W_wc ∧ actionA (codeMat 266) (codeMat 358) X = codeMat 228
    exact ⟨codeMat 383, hw, hact⟩
  · subst h2
    have hw : codeMat 1 ∈ o201W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [340, 132, 32, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 358) (codeMat 1) = codeMat 16 := by
      unfold actionA; rw [o348from201_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 158 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o201W_wc ∧ actionA (codeMat 266) (codeMat 358) X = codeMat 16
    exact ⟨codeMat 1, hw, hact⟩
  · subst h3
    have hw : codeMat 32 ∈ o201W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [340, 132, 32, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 266) (codeMat 358) (codeMat 32) = codeMat 1 := by
      unfold actionA; rw [o348from201_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 158 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o201W_wc ∧ actionA (codeMat 266) (codeMat 358) X = codeMat 1
    exact ⟨codeMat 32, hw, hact⟩

theorem orbit348_lb16_mono : QuotientRankAtLeast o348W_mono 16 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 358 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 358) o201W_wc) 16 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 358) hP hQ o201W_wc 16
      step109_orbit201_lb16_wc
  exact quotientRankAtLeast_mono o348W_le_action_201 hAct

end QiushiMatmul
