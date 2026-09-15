import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit72Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

def o158W_mono : Submodule F2 Mat3 := spanCodes [192, 32, 20, 10, 1]

private theorem o158from72_QtInv :
    (codeMat 345 : Mat3).transpose⁻¹ = (codeMat 345 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 345 : Mat3).transpose * (codeMat 345 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o158W_le_action_72 :
    o158W_mono ≤ actionW (codeMat 339) (codeMat 345) o72W_wc := by
  unfold o158W_mono
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 365 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 365 (by decide)
    have hact : actionA (codeMat 339) (codeMat 345) (codeMat 365) = codeMat 192 := by
      unfold actionA; rw [o158from72_QtInv]
      show (codeMat 339 : Mat3).transpose * codeMat 365 * (codeMat 345 : Mat3).transpose = codeMat 192
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o72W_wc ∧ actionA (codeMat 339) (codeMat 345) X = codeMat 192
    exact ⟨codeMat 365, hw, hact⟩
  · subst h1
    have hw : codeMat 32 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 339) (codeMat 345) (codeMat 32) = codeMat 32 := by
      unfold actionA; rw [o158from72_QtInv]
      show (codeMat 339 : Mat3).transpose * codeMat 32 * (codeMat 345 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o72W_wc ∧ actionA (codeMat 339) (codeMat 345) X = codeMat 32
    exact ⟨codeMat 32, hw, hact⟩
  · subst h2
    have hw : codeMat 52 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 52 (by decide)
    have hact : actionA (codeMat 339) (codeMat 345) (codeMat 52) = codeMat 20 := by
      unfold actionA; rw [o158from72_QtInv]
      show (codeMat 339 : Mat3).transpose * codeMat 52 * (codeMat 345 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o72W_wc ∧ actionA (codeMat 339) (codeMat 345) X = codeMat 20
    exact ⟨codeMat 52, hw, hact⟩
  · subst h3
    have hw : codeMat 42 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 42 (by decide)
    have hact : actionA (codeMat 339) (codeMat 345) (codeMat 42) = codeMat 10 := by
      unfold actionA; rw [o158from72_QtInv]
      show (codeMat 339 : Mat3).transpose * codeMat 42 * (codeMat 345 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o72W_wc ∧ actionA (codeMat 339) (codeMat 345) X = codeMat 10
    exact ⟨codeMat 42, hw, hact⟩
  · subst h4
    have hw : codeMat 63 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 63 (by decide)
    have hact : actionA (codeMat 339) (codeMat 345) (codeMat 63) = codeMat 1 := by
      unfold actionA; rw [o158from72_QtInv]
      show (codeMat 339 : Mat3).transpose * codeMat 63 * (codeMat 345 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o72W_wc ∧ actionA (codeMat 339) (codeMat 345) X = codeMat 1
    exact ⟨codeMat 63, hw, hact⟩

theorem orbit158_lb15_mono : QuotientRankAtLeast o158W_mono 15 := by
  have hP : Invertible (codeMat 339 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 345 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 339) (codeMat 345) o72W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 339) (codeMat 345) hP hQ o72W_wc 15
      step109_orbit72_lb15_wc
  exact quotientRankAtLeast_mono o158W_le_action_72 hAct

end QiushiMatmul
