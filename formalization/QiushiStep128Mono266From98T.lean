import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiMonoOrbit98From31T

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private def o98W_T : Submodule F2 Mat3 := spanCodes [80, 32, 8, 2, 1]

private theorem o98W_T_lb : QuotientRankAtLeast o98W_T 15 := by
  have ht := quotientRankAtLeast_transpose orbit98_lb15_mono
  have hle : o98W_T ≤ transposeW o98W_mono := by
    unfold o98W_T transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4
    · subst h0
      show codeMat 80 ∈ Submodule.map transposeLinearMap o98W_mono
      exact ⟨codeMat 20, spanContainsCodeCore_implies_mem_spanCodes [128, 20, 8, 2, 1] 20 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 32 ∈ Submodule.map transposeLinearMap o98W_mono
      exact ⟨codeMat 128, spanContainsCodeCore_implies_mem_spanCodes [128, 20, 8, 2, 1] 128 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 8 ∈ Submodule.map transposeLinearMap o98W_mono
      exact ⟨codeMat 2, spanContainsCodeCore_implies_mem_spanCodes [128, 20, 8, 2, 1] 2 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 2 ∈ Submodule.map transposeLinearMap o98W_mono
      exact ⟨codeMat 8, spanContainsCodeCore_implies_mem_spanCodes [128, 20, 8, 2, 1] 8 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 1 ∈ Submodule.map transposeLinearMap o98W_mono
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [128, 20, 8, 2, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

def o266W_mono : Submodule F2 Mat3 := spanCodes [80, 32, 2, 1]

private theorem o266from98_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o266W_le_action_98 :
    o266W_mono ≤ actionW (codeMat 273) (codeMat 273) o98W_T := by
  unfold o266W_mono
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    have hw : codeMat 80 ∈ o98W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [80, 32, 8, 2, 1] 80 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 80) = codeMat 80 := by
      unfold actionA; rw [o266from98_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 80 * (codeMat 273 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o98W_T ∧ actionA (codeMat 273) (codeMat 273) X = codeMat 80
    exact ⟨codeMat 80, hw, hact⟩
  · subst h1
    have hw : codeMat 32 ∈ o98W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [80, 32, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 32) = codeMat 32 := by
      unfold actionA; rw [o266from98_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 32 * (codeMat 273 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o98W_T ∧ actionA (codeMat 273) (codeMat 273) X = codeMat 32
    exact ⟨codeMat 32, hw, hact⟩
  · subst h2
    have hw : codeMat 2 ∈ o98W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [80, 32, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 2) = codeMat 2 := by
      unfold actionA; rw [o266from98_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o98W_T ∧ actionA (codeMat 273) (codeMat 273) X = codeMat 2
    exact ⟨codeMat 2, hw, hact⟩
  · subst h3
    have hw : codeMat 1 ∈ o98W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [80, 32, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA; rw [o266from98_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o98W_T ∧ actionA (codeMat 273) (codeMat 273) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩

theorem orbit266_lb15_mono : QuotientRankAtLeast o266W_mono 15 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 273) o98W_T) 15 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 273) hP hQ o98W_T 15
      o98W_T_lb
  exact quotientRankAtLeast_mono o266W_le_action_98 hAct

end QiushiMatmul
