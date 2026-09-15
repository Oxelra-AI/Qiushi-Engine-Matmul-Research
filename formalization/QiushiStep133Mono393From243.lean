import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiStep126Mono243From85

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

def o393W_mono : Submodule F2 Mat3 := spanCodes [262, 68, 20, 10]

private theorem o393from243_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o393W_le_action_243 :
    o393W_mono ≤ actionW (codeMat 141) (codeMat 273) o243W_mono := by
  unfold o393W_mono
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    have hw : codeMat 20 ∈ o243W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [131, 68, 35, 20, 10] 20 (by decide)
    have hact : actionA (codeMat 141) (codeMat 273) (codeMat 20) = codeMat 262 := by
      unfold actionA; rw [o393from243_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 20 * (codeMat 273 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o243W_mono ∧ actionA (codeMat 141) (codeMat 273) X = codeMat 262
    exact ⟨codeMat 20, hw, hact⟩
  · subst h1
    have hw : codeMat 41 ∈ o243W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [131, 68, 35, 20, 10] 41 (by decide)
    have hact : actionA (codeMat 141) (codeMat 273) (codeMat 41) = codeMat 68 := by
      unfold actionA; rw [o393from243_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 41 * (codeMat 273 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o243W_mono ∧ actionA (codeMat 141) (codeMat 273) X = codeMat 68
    exact ⟨codeMat 41, hw, hact⟩
  · subst h2
    have hw : codeMat 160 ∈ o243W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [131, 68, 35, 20, 10] 160 (by decide)
    have hact : actionA (codeMat 141) (codeMat 273) (codeMat 160) = codeMat 20 := by
      unfold actionA; rw [o393from243_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 160 * (codeMat 273 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o243W_mono ∧ actionA (codeMat 141) (codeMat 273) X = codeMat 20
    exact ⟨codeMat 160, hw, hact⟩
  · subst h3
    have hw : codeMat 80 ∈ o243W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [131, 68, 35, 20, 10] 80 (by decide)
    have hact : actionA (codeMat 141) (codeMat 273) (codeMat 80) = codeMat 10 := by
      unfold actionA; rw [o393from243_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 80 * (codeMat 273 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o243W_mono ∧ actionA (codeMat 141) (codeMat 273) X = codeMat 10
    exact ⟨codeMat 80, hw, hact⟩

theorem orbit393_lb17_mono : QuotientRankAtLeast o393W_mono 17 := by
  have hP : Invertible (codeMat 141 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 141) (codeMat 273) o243W_mono) 17 :=
    @quotientRankAtLeast_action (codeMat 141) (codeMat 273) hP hQ o243W_mono 17
      orbit243_lb17_mono
  exact quotientRankAtLeast_mono o393W_le_action_243 hAct

end QiushiMatmul
