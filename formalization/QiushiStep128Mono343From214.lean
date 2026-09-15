import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit214Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

def o343W_mono : Submodule F2 Mat3 := spanCodes [298, 100, 16, 1]

private theorem o343from214_QtInv :
    (codeMat 331 : Mat3).transpose⁻¹ = (codeMat 410 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 331 : Mat3).transpose * (codeMat 410 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o343W_le_action_214 :
    o343W_mono ≤ actionW (codeMat 354) (codeMat 331) o214W_wc := by
  unfold o343W_mono
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    have hw : codeMat 107 ∈ o214W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 107 (by decide)
    have hact : actionA (codeMat 354) (codeMat 331) (codeMat 107) = codeMat 298 := by
      unfold actionA; rw [o343from214_QtInv]
      show (codeMat 354 : Mat3).transpose * codeMat 107 * (codeMat 410 : Mat3).transpose = codeMat 298
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o214W_wc ∧ actionA (codeMat 354) (codeMat 331) X = codeMat 298
    exact ⟨codeMat 107, hw, hact⟩
  · subst h1
    have hw : codeMat 284 ∈ o214W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 284 (by decide)
    have hact : actionA (codeMat 354) (codeMat 331) (codeMat 284) = codeMat 100 := by
      unfold actionA; rw [o343from214_QtInv]
      show (codeMat 354 : Mat3).transpose * codeMat 284 * (codeMat 410 : Mat3).transpose = codeMat 100
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o214W_wc ∧ actionA (codeMat 354) (codeMat 331) X = codeMat 100
    exact ⟨codeMat 284, hw, hact⟩
  · subst h2
    have hw : codeMat 1 ∈ o214W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 354) (codeMat 331) (codeMat 1) = codeMat 16 := by
      unfold actionA; rw [o343from214_QtInv]
      show (codeMat 354 : Mat3).transpose * codeMat 1 * (codeMat 410 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o214W_wc ∧ actionA (codeMat 354) (codeMat 331) X = codeMat 16
    exact ⟨codeMat 1, hw, hact⟩
  · subst h3
    have hw : codeMat 504 ∈ o214W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 504 (by decide)
    have hact : actionA (codeMat 354) (codeMat 331) (codeMat 504) = codeMat 1 := by
      unfold actionA; rw [o343from214_QtInv]
      show (codeMat 354 : Mat3).transpose * codeMat 504 * (codeMat 410 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o214W_wc ∧ actionA (codeMat 354) (codeMat 331) X = codeMat 1
    exact ⟨codeMat 504, hw, hact⟩

theorem orbit343_lb16_mono : QuotientRankAtLeast o343W_mono 16 := by
  have hP : Invertible (codeMat 354 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 331 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 354) (codeMat 331) o214W_wc) 16 :=
    @quotientRankAtLeast_action (codeMat 354) (codeMat 331) hP hQ o214W_wc 16
      step109_orbit214_lb16_wc
  exact quotientRankAtLeast_mono o343W_le_action_214 hAct

end QiushiMatmul
