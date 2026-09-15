import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiWcOrbit80Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private def o80W_T : Submodule F2 Mat3 := spanCodes [272, 132, 80, 36, 10, 1]

private theorem o80W_T_lb : QuotientRankAtLeast o80W_T 15 := by
  have ht := quotientRankAtLeast_transpose step109_orbit80_lb15_wc
  have hle : o80W_T ≤ transposeW o80W_wc := by
    unfold o80W_T transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4 | h5
    · subst h0
      show codeMat 272 ∈ Submodule.map transposeLinearMap o80W_wc
      exact ⟨codeMat 272, spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 272 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 132 ∈ Submodule.map transposeLinearMap o80W_wc
      exact ⟨codeMat 96, spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 96 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 80 ∈ Submodule.map transposeLinearMap o80W_wc
      exact ⟨codeMat 20, spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 20 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 36 ∈ Submodule.map transposeLinearMap o80W_wc
      exact ⟨codeMat 192, spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 192 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 10 ∈ Submodule.map transposeLinearMap o80W_wc
      exact ⟨codeMat 10, spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 10 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h5
      show codeMat 1 ∈ Submodule.map transposeLinearMap o80W_wc
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

def o189W_mono : Submodule F2 Mat3 := spanCodes [278, 128, 32, 10, 1]

private theorem o189from80_QtInv :
    (codeMat 460 : Mat3).transpose⁻¹ = (codeMat 122 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 460 : Mat3).transpose * (codeMat 122 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o189W_le_action_80 :
    o189W_mono ≤ actionW (codeMat 159) (codeMat 460) o80W_T := by
  unfold o189W_mono
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 357 ∈ o80W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 36, 10, 1] 357 (by decide)
    have hact : actionA (codeMat 159) (codeMat 460) (codeMat 357) = codeMat 278 := by
      unfold actionA; rw [o189from80_QtInv]
      show (codeMat 159 : Mat3).transpose * codeMat 357 * (codeMat 122 : Mat3).transpose = codeMat 278
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o80W_T ∧ actionA (codeMat 159) (codeMat 460) X = codeMat 278
    exact ⟨codeMat 357, hw, hact⟩
  · subst h1
    have hw : codeMat 36 ∈ o80W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 36, 10, 1] 36 (by decide)
    have hact : actionA (codeMat 159) (codeMat 460) (codeMat 36) = codeMat 128 := by
      unfold actionA; rw [o189from80_QtInv]
      show (codeMat 159 : Mat3).transpose * codeMat 36 * (codeMat 122 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o80W_T ∧ actionA (codeMat 159) (codeMat 460) X = codeMat 128
    exact ⟨codeMat 36, hw, hact⟩
  · subst h2
    have hw : codeMat 320 ∈ o80W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 36, 10, 1] 320 (by decide)
    have hact : actionA (codeMat 159) (codeMat 460) (codeMat 320) = codeMat 32 := by
      unfold actionA; rw [o189from80_QtInv]
      show (codeMat 159 : Mat3).transpose * codeMat 320 * (codeMat 122 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o80W_T ∧ actionA (codeMat 159) (codeMat 460) X = codeMat 32
    exact ⟨codeMat 320, hw, hact⟩
  · subst h3
    have hw : codeMat 160 ∈ o80W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 36, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 159) (codeMat 460) (codeMat 160) = codeMat 10 := by
      unfold actionA; rw [o189from80_QtInv]
      show (codeMat 159 : Mat3).transpose * codeMat 160 * (codeMat 122 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o80W_T ∧ actionA (codeMat 159) (codeMat 460) X = codeMat 10
    exact ⟨codeMat 160, hw, hact⟩
  · subst h4
    have hw : codeMat 432 ∈ o80W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 36, 10, 1] 432 (by decide)
    have hact : actionA (codeMat 159) (codeMat 460) (codeMat 432) = codeMat 1 := by
      unfold actionA; rw [o189from80_QtInv]
      show (codeMat 159 : Mat3).transpose * codeMat 432 * (codeMat 122 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ o80W_T ∧ actionA (codeMat 159) (codeMat 460) X = codeMat 1
    exact ⟨codeMat 432, hw, hact⟩

theorem orbit189_lb15_mono : QuotientRankAtLeast o189W_mono 15 := by
  have hP : Invertible (codeMat 159 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 460 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 159) (codeMat 460) o80W_T) 15 :=
    @quotientRankAtLeast_action (codeMat 159) (codeMat 460) hP hQ o80W_T 15
      o80W_T_lb
  exact quotientRankAtLeast_mono o189W_le_action_80 hAct

end QiushiMatmul
