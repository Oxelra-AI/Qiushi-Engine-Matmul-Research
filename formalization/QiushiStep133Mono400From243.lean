import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiStep126Mono243From85

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

def o400W_mono : Submodule F2 Mat3 := spanCodes [259, 96, 20, 10]

private theorem o400from243_QtInv :
    (codeMat 156 : Mat3).transpose⁻¹ = (codeMat 102 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 156 : Mat3).transpose * (codeMat 102 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o400W_le_action_243 :
    o400W_mono ≤ actionW (codeMat 281) (codeMat 156) o243W_mono := by
  unfold o400W_mono
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    have hw : codeMat 68 ∈ o243W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [131, 68, 35, 20, 10] 68 (by decide)
    have hact : actionA (codeMat 281) (codeMat 156) (codeMat 68) = codeMat 259 := by
      unfold actionA; rw [o400from243_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 68 * (codeMat 102 : Mat3).transpose = codeMat 259
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o243W_mono ∧ actionA (codeMat 281) (codeMat 156) X = codeMat 259
    exact ⟨codeMat 68, hw, hact⟩
  · subst h1
    have hw : codeMat 137 ∈ o243W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [131, 68, 35, 20, 10] 137 (by decide)
    have hact : actionA (codeMat 281) (codeMat 156) (codeMat 137) = codeMat 96 := by
      unfold actionA; rw [o400from243_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 137 * (codeMat 102 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o243W_mono ∧ actionA (codeMat 281) (codeMat 156) X = codeMat 96
    exact ⟨codeMat 137, hw, hact⟩
  · subst h2
    have hw : codeMat 55 ∈ o243W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [131, 68, 35, 20, 10] 55 (by decide)
    have hact : actionA (codeMat 281) (codeMat 156) (codeMat 55) = codeMat 20 := by
      unfold actionA; rw [o400from243_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 55 * (codeMat 102 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o243W_mono ∧ actionA (codeMat 281) (codeMat 156) X = codeMat 20
    exact ⟨codeMat 55, hw, hact⟩
  · subst h3
    have hw : codeMat 20 ∈ o243W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [131, 68, 35, 20, 10] 20 (by decide)
    have hact : actionA (codeMat 281) (codeMat 156) (codeMat 20) = codeMat 10 := by
      unfold actionA; rw [o400from243_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 20 * (codeMat 102 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o243W_mono ∧ actionA (codeMat 281) (codeMat 156) X = codeMat 10
    exact ⟨codeMat 20, hw, hact⟩

theorem orbit400_lb17_mono : QuotientRankAtLeast o400W_mono 17 := by
  have hP : Invertible (codeMat 281 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 156 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 281) (codeMat 156) o243W_mono) 17 :=
    @quotientRankAtLeast_action (codeMat 281) (codeMat 156) hP hQ o243W_mono 17
      orbit243_lb17_mono
  exact quotientRankAtLeast_mono o400W_le_action_243 hAct

end QiushiMatmul
