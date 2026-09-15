import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit96Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

def o294W_mono : Submodule F2 Mat3 := spanCodes [258, 32, 10, 1]

private theorem o294from96_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o294W_le_action_96 :
    o294W_mono ≤ actionW (codeMat 273) (codeMat 140) o96W_wc := by
  unfold o294W_mono
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    have hw : codeMat 68 ∈ o96W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [68, 20, 8, 2, 1] 68 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 68) = codeMat 258 := by
      unfold actionA; rw [o294from96_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 68 * (codeMat 98 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o96W_wc ∧ actionA (codeMat 273) (codeMat 140) X = codeMat 258
    exact ⟨codeMat 68, hw, hact⟩
  · subst h1
    have hw : codeMat 8 ∈ o96W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [68, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 8) = codeMat 32 := by
      unfold actionA; rw [o294from96_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o96W_wc ∧ actionA (codeMat 273) (codeMat 140) X = codeMat 32
    exact ⟨codeMat 8, hw, hact⟩
  · subst h2
    have hw : codeMat 20 ∈ o96W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [68, 20, 8, 2, 1] 20 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 20) = codeMat 10 := by
      unfold actionA; rw [o294from96_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 20 * (codeMat 98 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o96W_wc ∧ actionA (codeMat 273) (codeMat 140) X = codeMat 10
    exact ⟨codeMat 20, hw, hact⟩
  · subst h3
    have hw : codeMat 2 ∈ o96W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [68, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 2) = codeMat 1 := by
      unfold actionA; rw [o294from96_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o96W_wc ∧ actionA (codeMat 273) (codeMat 140) X = codeMat 1
    exact ⟨codeMat 2, hw, hact⟩

theorem orbit294_lb16_mono : QuotientRankAtLeast o294W_mono 16 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 140) o96W_wc) 16 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 140) hP hQ o96W_wc 16
      step109_orbit96_lb16_wc
  exact quotientRankAtLeast_mono o294W_le_action_96 hAct

end QiushiMatmul
