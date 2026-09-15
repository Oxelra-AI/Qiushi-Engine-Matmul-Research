import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiStep126Mono243From85

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

def o397W_mono : Submodule F2 Mat3 := spanCodes [135, 96, 20, 10]

private theorem o397from243_QtInv :
    (codeMat 485 : Mat3).transpose⁻¹ = (codeMat 171 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 485 : Mat3).transpose * (codeMat 171 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o397W_le_action_243 :
    o397W_mono ≤ actionW (codeMat 110) (codeMat 485) o243W_mono := by
  unfold o397W_mono
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    have hw : codeMat 160 ∈ o243W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [131, 68, 35, 20, 10] 160 (by decide)
    have hact : actionA (codeMat 110) (codeMat 485) (codeMat 160) = codeMat 135 := by
      unfold actionA; rw [o397from243_QtInv]
      show (codeMat 110 : Mat3).transpose * codeMat 160 * (codeMat 171 : Mat3).transpose = codeMat 135
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o243W_mono ∧ actionA (codeMat 110) (codeMat 485) X = codeMat 135
    exact ⟨codeMat 160, hw, hact⟩
  · subst h1
    have hw : codeMat 151 ∈ o243W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [131, 68, 35, 20, 10] 151 (by decide)
    have hact : actionA (codeMat 110) (codeMat 485) (codeMat 151) = codeMat 96 := by
      unfold actionA; rw [o397from243_QtInv]
      show (codeMat 110 : Mat3).transpose * codeMat 151 * (codeMat 171 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o243W_mono ∧ actionA (codeMat 110) (codeMat 485) X = codeMat 96
    exact ⟨codeMat 151, hw, hact⟩
  · subst h2
    have hw : codeMat 228 ∈ o243W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [131, 68, 35, 20, 10] 228 (by decide)
    have hact : actionA (codeMat 110) (codeMat 485) (codeMat 228) = codeMat 20 := by
      unfold actionA; rw [o397from243_QtInv]
      show (codeMat 110 : Mat3).transpose * codeMat 228 * (codeMat 171 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o243W_mono ∧ actionA (codeMat 110) (codeMat 485) X = codeMat 20
    exact ⟨codeMat 228, hw, hact⟩
  · subst h3
    have hw : codeMat 109 ∈ o243W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [131, 68, 35, 20, 10] 109 (by decide)
    have hact : actionA (codeMat 110) (codeMat 485) (codeMat 109) = codeMat 10 := by
      unfold actionA; rw [o397from243_QtInv]
      show (codeMat 110 : Mat3).transpose * codeMat 109 * (codeMat 171 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o243W_mono ∧ actionA (codeMat 110) (codeMat 485) X = codeMat 10
    exact ⟨codeMat 109, hw, hact⟩

theorem orbit397_lb17_mono : QuotientRankAtLeast o397W_mono 17 := by
  have hP : Invertible (codeMat 110 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 485 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 110) (codeMat 485) o243W_mono) 17 :=
    @quotientRankAtLeast_action (codeMat 110) (codeMat 485) hP hQ o243W_mono 17
      orbit243_lb17_mono
  exact quotientRankAtLeast_mono o397W_le_action_243 hAct

end QiushiMatmul
