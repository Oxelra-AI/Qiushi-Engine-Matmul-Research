import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiOrbit31FP

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private def o31W_T : Submodule F2 Mat3 := spanCodes [128, 68, 20, 8, 2, 1]

private theorem o31W_T_lb : QuotientRankAtLeast o31W_T 15 := by
  have ht := quotientRankAtLeast_transpose orbit31_lb15
  have hle : o31W_T ≤ transposeW orbit31W := by
    unfold o31W_T transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4 | h5
    · subst h0
      show codeMat 128 ∈ Submodule.map transposeLinearMap orbit31W
      exact ⟨codeMat 32, spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 32 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 68 ∈ Submodule.map transposeLinearMap orbit31W
      exact ⟨codeMat 68, spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 68 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 20 ∈ Submodule.map transposeLinearMap orbit31W
      exact ⟨codeMat 80, spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 80 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 8 ∈ Submodule.map transposeLinearMap orbit31W
      exact ⟨codeMat 2, spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 2 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 2 ∈ Submodule.map transposeLinearMap orbit31W
      exact ⟨codeMat 8, spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 8 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h5
      show codeMat 1 ∈ Submodule.map transposeLinearMap orbit31W
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem o98from31_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o98from31_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 98, basis [128, 20, 8, 2, 1]. -/
def o98W_mono : Submodule F2 Mat3 := spanCodes [128, 20, 8, 2, 1]

private theorem o98from31_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o98W_le_action_31 :
    o98W_mono ≤ actionW (codeMat 161) (codeMat 266) o31W_T := by
  apply o98from31_spanCodes_le_of_gens [128, 20, 8, 2, 1]
    (actionW (codeMat 161) (codeMat 266) o31W_T)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 8 ∈ o31W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 8) = codeMat 128 := by
      unfold actionA
      rw [o98from31_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 8 * (codeMat 266 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o98from31_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 68 ∈ o31W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 20, 8, 2, 1] 68 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 68) = codeMat 20 := by
      unfold actionA
      rw [o98from31_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 68 * (codeMat 266 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o98from31_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 128 ∈ o31W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 128) = codeMat 8 := by
      unfold actionA
      rw [o98from31_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 128 * (codeMat 266 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o98from31_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o31W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 1) = codeMat 2 := by
      unfold actionA
      rw [o98from31_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o98from31_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o31W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [o98from31_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o98from31_codeMat_mem_actionW_of_witness hw hact

theorem orbit98_lb15_mono : QuotientRankAtLeast o98W_mono 15 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 266) o31W_T) 15 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 266) hP hQ o31W_T 15
      o31W_T_lb
  exact quotientRankAtLeast_mono o98W_le_action_31 hAct

end QiushiMatmul
