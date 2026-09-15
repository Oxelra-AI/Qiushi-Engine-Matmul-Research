import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit157Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

def o325W_mono : Submodule F2 Mat3 := spanCodes [448, 36, 16, 1]

private theorem o325from157_QtInv :
    (codeMat 358 : Mat3).transpose⁻¹ = (codeMat 158 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 358 : Mat3).transpose * (codeMat 158 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o325W_le_action_157 :
    o325W_mono ≤ actionW (codeMat 266) (codeMat 358) o157W_wc := by
  unfold o325W_mono
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    have hw : codeMat 128 ∈ o157W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 266) (codeMat 358) (codeMat 128) = codeMat 448 := by
      unfold actionA; rw [o325from157_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 128 * (codeMat 158 : Mat3).transpose = codeMat 448
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o157W_wc ∧ actionA (codeMat 266) (codeMat 358) X = codeMat 448
    exact ⟨codeMat 128, hw, hact⟩
  · subst h1
    have hw : codeMat 63 ∈ o157W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 10, 1] 63 (by decide)
    have hact : actionA (codeMat 266) (codeMat 358) (codeMat 63) = codeMat 36 := by
      unfold actionA; rw [o325from157_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 63 * (codeMat 158 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o157W_wc ∧ actionA (codeMat 266) (codeMat 358) X = codeMat 36
    exact ⟨codeMat 63, hw, hact⟩
  · subst h2
    have hw : codeMat 1 ∈ o157W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 358) (codeMat 1) = codeMat 16 := by
      unfold actionA; rw [o325from157_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 158 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o157W_wc ∧ actionA (codeMat 266) (codeMat 358) X = codeMat 16
    exact ⟨codeMat 1, hw, hact⟩
  · subst h3
    have hw : codeMat 32 ∈ o157W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 266) (codeMat 358) (codeMat 32) = codeMat 1 := by
      unfold actionA; rw [o325from157_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 158 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o157W_wc ∧ actionA (codeMat 266) (codeMat 358) X = codeMat 1
    exact ⟨codeMat 32, hw, hact⟩

theorem orbit325_lb15_mono : QuotientRankAtLeast o325W_mono 15 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 358 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 358) o157W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 358) hP hQ o157W_wc 15
      step109_orbit157_lb15_wc
  exact quotientRankAtLeast_mono o325W_le_action_157 hAct

end QiushiMatmul
