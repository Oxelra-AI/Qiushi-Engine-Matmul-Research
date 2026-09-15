import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit85Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

def o247W_mono : Submodule F2 Mat3 := spanCodes [259, 135, 96, 20, 10]

private theorem o247from85_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o247W_le_action_85 :
    o247W_mono ≤ actionW (codeMat 85) (codeMat 84) o85W_wc := by
  unfold o247W_mono
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 449 ∈ o85W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 131, 68, 35, 20, 10] 449 (by decide)
    have hact : actionA (codeMat 85) (codeMat 84) (codeMat 449) = codeMat 259 := by
      unfold actionA; rw [o247from85_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 449 * (codeMat 84 : Mat3).transpose = codeMat 259
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o85W_wc ∧ actionA (codeMat 85) (codeMat 84) X = codeMat 259
    exact ⟨codeMat 449, hw, hact⟩
  · subst h1
    have hw : codeMat 322 ∈ o85W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 131, 68, 35, 20, 10] 322 (by decide)
    have hact : actionA (codeMat 85) (codeMat 84) (codeMat 322) = codeMat 135 := by
      unfold actionA; rw [o247from85_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 322 * (codeMat 84 : Mat3).transpose = codeMat 135
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o85W_wc ∧ actionA (codeMat 85) (codeMat 84) X = codeMat 135
    exact ⟨codeMat 322, hw, hact⟩
  · subst h2
    have hw : codeMat 268 ∈ o85W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 131, 68, 35, 20, 10] 268 (by decide)
    have hact : actionA (codeMat 85) (codeMat 84) (codeMat 268) = codeMat 96 := by
      unfold actionA; rw [o247from85_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 268 * (codeMat 84 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o85W_wc ∧ actionA (codeMat 85) (codeMat 84) X = codeMat 96
    exact ⟨codeMat 268, hw, hact⟩
  · subst h3
    have hw : codeMat 80 ∈ o85W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 131, 68, 35, 20, 10] 80 (by decide)
    have hact : actionA (codeMat 85) (codeMat 84) (codeMat 80) = codeMat 20 := by
      unfold actionA; rw [o247from85_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 80 * (codeMat 84 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o85W_wc ∧ actionA (codeMat 85) (codeMat 84) X = codeMat 20
    exact ⟨codeMat 80, hw, hact⟩
  · subst h4
    have hw : codeMat 160 ∈ o85W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 131, 68, 35, 20, 10] 160 (by decide)
    have hact : actionA (codeMat 85) (codeMat 84) (codeMat 160) = codeMat 10 := by
      unfold actionA; rw [o247from85_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 160 * (codeMat 84 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o85W_wc ∧ actionA (codeMat 85) (codeMat 84) X = codeMat 10
    exact ⟨codeMat 160, hw, hact⟩

theorem orbit247_lb17_mono : QuotientRankAtLeast o247W_mono 17 := by
  have hP : Invertible (codeMat 85 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 85) (codeMat 84) o85W_wc) 17 :=
    @quotientRankAtLeast_action (codeMat 85) (codeMat 84) hP hQ o85W_wc 17
      step109_orbit85_lb17_wc
  exact quotientRankAtLeast_mono o247W_le_action_85 hAct

end QiushiMatmul
