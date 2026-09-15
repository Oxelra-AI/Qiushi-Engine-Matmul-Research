import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiOrbit35FP

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private def o35W_T : Submodule F2 Mat3 := spanCodes [132, 80, 32, 8, 2, 1]

private theorem o35W_T_lb : QuotientRankAtLeast o35W_T 15 := by
  have ht := quotientRankAtLeast_transpose orbit35_lb15
  have hle : o35W_T ≤ transposeW orbit35W := by
    unfold o35W_T transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4 | h5
    · subst h0
      show codeMat 132 ∈ Submodule.map transposeLinearMap orbit35W
      exact ⟨codeMat 96, spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 96 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 80 ∈ Submodule.map transposeLinearMap orbit35W
      exact ⟨codeMat 20, spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 20 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 32 ∈ Submodule.map transposeLinearMap orbit35W
      exact ⟨codeMat 128, spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 128 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 8 ∈ Submodule.map transposeLinearMap orbit35W
      exact ⟨codeMat 2, spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 2 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 2 ∈ Submodule.map transposeLinearMap orbit35W
      exact ⟨codeMat 8, spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 8 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h5
      show codeMat 1 ∈ Submodule.map transposeLinearMap orbit35W
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem o112from35_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o112from35_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 112, basis [272, 96, 8, 2, 1]. -/
def o112W_mono : Submodule F2 Mat3 := spanCodes [272, 96, 8, 2, 1]

private theorem o112from35_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o112W_le_action_35 :
    o112W_mono ≤ actionW (codeMat 267) (codeMat 161) o35W_T := by
  apply o112from35_spanCodes_le_of_gens [272, 96, 8, 2, 1]
    (actionW (codeMat 267) (codeMat 161) o35W_T)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 164 ∈ o35W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 80, 32, 8, 2, 1] 164 (by decide)
    have hact : actionA (codeMat 267) (codeMat 161) (codeMat 164) = codeMat 272 := by
      unfold actionA
      rw [o112from35_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 164 * (codeMat 161 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o112from35_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 82 ∈ o35W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 80, 32, 8, 2, 1] 82 (by decide)
    have hact : actionA (codeMat 267) (codeMat 161) (codeMat 82) = codeMat 96 := by
      unfold actionA
      rw [o112from35_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 82 * (codeMat 161 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o112from35_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 9 ∈ o35W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 80, 32, 8, 2, 1] 9 (by decide)
    have hact : actionA (codeMat 267) (codeMat 161) (codeMat 9) = codeMat 8 := by
      unfold actionA
      rw [o112from35_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 9 * (codeMat 161 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o112from35_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 32 ∈ o35W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 80, 32, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 267) (codeMat 161) (codeMat 32) = codeMat 2 := by
      unfold actionA
      rw [o112from35_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 32 * (codeMat 161 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o112from35_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ o35W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 80, 32, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 267) (codeMat 161) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [o112from35_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 8 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o112from35_codeMat_mem_actionW_of_witness hw hact

theorem orbit112_lb15_mono : QuotientRankAtLeast o112W_mono 15 := by
  have hP : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 267) (codeMat 161) o35W_T) 15 :=
    @quotientRankAtLeast_action (codeMat 267) (codeMat 161) hP hQ o35W_T 15
      o35W_T_lb
  exact quotientRankAtLeast_mono o112W_le_action_35 hAct

end QiushiMatmul
