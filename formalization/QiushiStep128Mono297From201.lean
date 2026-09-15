import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit201Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

def o297W_mono : Submodule F2 Mat3 := spanCodes [336, 32, 10, 1]

private theorem o297from201_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o297W_le_action_201 :
    o297W_mono ≤ actionW (codeMat 337) (codeMat 273) o201W_wc := by
  unfold o297W_mono
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    have hw : codeMat 341 ∈ o201W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [340, 132, 32, 10, 1] 341 (by decide)
    have hact : actionA (codeMat 337) (codeMat 273) (codeMat 341) = codeMat 336 := by
      unfold actionA; rw [o297from201_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 341 * (codeMat 273 : Mat3).transpose = codeMat 336
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o201W_wc ∧ actionA (codeMat 337) (codeMat 273) X = codeMat 336
    exact ⟨codeMat 341, hw, hact⟩
  · subst h1
    have hw : codeMat 32 ∈ o201W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [340, 132, 32, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 337) (codeMat 273) (codeMat 32) = codeMat 32 := by
      unfold actionA; rw [o297from201_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 32 * (codeMat 273 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o201W_wc ∧ actionA (codeMat 337) (codeMat 273) X = codeMat 32
    exact ⟨codeMat 32, hw, hact⟩
  · subst h2
    have hw : codeMat 10 ∈ o201W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [340, 132, 32, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 337) (codeMat 273) (codeMat 10) = codeMat 10 := by
      unfold actionA; rw [o297from201_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 10 * (codeMat 273 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o201W_wc ∧ actionA (codeMat 337) (codeMat 273) X = codeMat 10
    exact ⟨codeMat 10, hw, hact⟩
  · subst h3
    have hw : codeMat 1 ∈ o201W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [340, 132, 32, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 337) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA; rw [o297from201_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o201W_wc ∧ actionA (codeMat 337) (codeMat 273) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩

theorem orbit297_lb16_mono : QuotientRankAtLeast o297W_mono 16 := by
  have hP : Invertible (codeMat 337 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 337) (codeMat 273) o201W_wc) 16 :=
    @quotientRankAtLeast_action (codeMat 337) (codeMat 273) hP hQ o201W_wc 16
      step109_orbit201_lb16_wc
  exact quotientRankAtLeast_mono o297W_le_action_201 hAct

end QiushiMatmul
