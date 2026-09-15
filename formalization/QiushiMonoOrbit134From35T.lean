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

private theorem o134from35_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o134from35_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 134, basis [156, 80, 32, 2, 1]. -/
def o134W_mono : Submodule F2 Mat3 := spanCodes [156, 80, 32, 2, 1]

private theorem o134from35_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = (codeMat 275 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * (codeMat 275 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o134W_le_action_35 :
    o134W_mono ≤ actionW (codeMat 273) (codeMat 275) o35W_T := by
  apply o134from35_spanCodes_le_of_gens [156, 80, 32, 2, 1]
    (actionW (codeMat 273) (codeMat 275) o35W_T)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 212 ∈ o35W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 80, 32, 8, 2, 1] 212 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 212) = codeMat 156 := by
      unfold actionA
      rw [o134from35_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 212 * (codeMat 275 : Mat3).transpose = codeMat 156
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o134from35_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 88 ∈ o35W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 80, 32, 8, 2, 1] 88 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 88) = codeMat 80 := by
      unfold actionA
      rw [o134from35_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 88 * (codeMat 275 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o134from35_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 32 ∈ o35W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 80, 32, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 32) = codeMat 32 := by
      unfold actionA
      rw [o134from35_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 32 * (codeMat 275 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o134from35_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 3 ∈ o35W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 80, 32, 8, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [o134from35_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 3 * (codeMat 275 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o134from35_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o35W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 80, 32, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [o134from35_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 275 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o134from35_codeMat_mem_actionW_of_witness hw hact

theorem orbit134_lb15_mono : QuotientRankAtLeast o134W_mono 15 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 275) o35W_T) 15 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 275) hP hQ o35W_T 15
      o35W_T_lb
  exact quotientRankAtLeast_mono o134W_le_action_35 hAct

end QiushiMatmul
