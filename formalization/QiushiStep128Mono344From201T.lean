import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiWcOrbit201Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private def o201W_T : Submodule F2 Mat3 := spanCodes [308, 128, 96, 10, 1]

private theorem o201W_T_lb : QuotientRankAtLeast o201W_T 16 := by
  have ht := quotientRankAtLeast_transpose step109_orbit201_lb16_wc
  have hle : o201W_T ≤ transposeW o201W_wc := by
    unfold o201W_T transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4
    · subst h0
      show codeMat 308 ∈ Submodule.map transposeLinearMap o201W_wc
      exact ⟨codeMat 464, spanContainsCodeCore_implies_mem_spanCodes [340, 132, 32, 10, 1] 464 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 128 ∈ Submodule.map transposeLinearMap o201W_wc
      exact ⟨codeMat 32, spanContainsCodeCore_implies_mem_spanCodes [340, 132, 32, 10, 1] 32 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 96 ∈ Submodule.map transposeLinearMap o201W_wc
      exact ⟨codeMat 132, spanContainsCodeCore_implies_mem_spanCodes [340, 132, 32, 10, 1] 132 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 10 ∈ Submodule.map transposeLinearMap o201W_wc
      exact ⟨codeMat 10, spanContainsCodeCore_implies_mem_spanCodes [340, 132, 32, 10, 1] 10 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 1 ∈ Submodule.map transposeLinearMap o201W_wc
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [340, 132, 32, 10, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

def o344W_mono : Submodule F2 Mat3 := spanCodes [386, 100, 16, 1]

private theorem o344from201_QtInv :
    (codeMat 270 : Mat3).transpose⁻¹ = (codeMat 298 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 270 : Mat3).transpose * (codeMat 298 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o344W_le_action_201 :
    o344W_mono ≤ actionW (codeMat 98) (codeMat 270) o201W_T := by
  unfold o344W_mono
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    have hw : codeMat 96 ∈ o201W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [308, 128, 96, 10, 1] 96 (by decide)
    have hact : actionA (codeMat 98) (codeMat 270) (codeMat 96) = codeMat 386 := by
      unfold actionA; rw [o344from201_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 96 * (codeMat 298 : Mat3).transpose = codeMat 386
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o201W_T ∧ actionA (codeMat 98) (codeMat 270) X = codeMat 386
    exact ⟨codeMat 96, hw, hact⟩
  · subst h1
    have hw : codeMat 341 ∈ o201W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [308, 128, 96, 10, 1] 341 (by decide)
    have hact : actionA (codeMat 98) (codeMat 270) (codeMat 341) = codeMat 100 := by
      unfold actionA; rw [o344from201_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 341 * (codeMat 298 : Mat3).transpose = codeMat 100
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o201W_T ∧ actionA (codeMat 98) (codeMat 270) X = codeMat 100
    exact ⟨codeMat 341, hw, hact⟩
  · subst h2
    have hw : codeMat 1 ∈ o201W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [308, 128, 96, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 98) (codeMat 270) (codeMat 1) = codeMat 16 := by
      unfold actionA; rw [o344from201_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 1 * (codeMat 298 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o201W_T ∧ actionA (codeMat 98) (codeMat 270) X = codeMat 16
    exact ⟨codeMat 1, hw, hact⟩
  · subst h3
    have hw : codeMat 128 ∈ o201W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [308, 128, 96, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 98) (codeMat 270) (codeMat 128) = codeMat 1 := by
      unfold actionA; rw [o344from201_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 128 * (codeMat 298 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o201W_T ∧ actionA (codeMat 98) (codeMat 270) X = codeMat 1
    exact ⟨codeMat 128, hw, hact⟩

theorem orbit344_lb16_mono : QuotientRankAtLeast o344W_mono 16 := by
  have hP : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 270 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 98) (codeMat 270) o201W_T) 16 :=
    @quotientRankAtLeast_action (codeMat 98) (codeMat 270) hP hQ o201W_T 16
      o201W_T_lb
  exact quotientRankAtLeast_mono o344W_le_action_201 hAct

end QiushiMatmul
