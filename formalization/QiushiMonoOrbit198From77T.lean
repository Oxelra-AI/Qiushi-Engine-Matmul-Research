import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiStep99Orbit77Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private def o77W_T : Submodule F2 Mat3 := spanCodes [272, 132, 80, 32, 10, 1]

private theorem o77W_T_lb : QuotientRankAtLeast o77W_T 15 := by
  have ht := quotientRankAtLeast_transpose step99_orbit77_lb15_unconditional
  have hle : o77W_T ≤ transposeW o77W := by
    unfold o77W_T transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4 | h5
    · subst h0
      show codeMat 272 ∈ Submodule.map transposeLinearMap o77W
      exact ⟨codeMat 272, spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 272 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 132 ∈ Submodule.map transposeLinearMap o77W
      exact ⟨codeMat 96, spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 96 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 80 ∈ Submodule.map transposeLinearMap o77W
      exact ⟨codeMat 20, spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 20 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 32 ∈ Submodule.map transposeLinearMap o77W
      exact ⟨codeMat 128, spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 128 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 10 ∈ Submodule.map transposeLinearMap o77W
      exact ⟨codeMat 10, spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 10 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h5
      show codeMat 1 ∈ Submodule.map transposeLinearMap o77W
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem o198from77_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o198from77_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 198, basis [326, 132, 32, 10, 1]. -/
def o198W_mono : Submodule F2 Mat3 := spanCodes [326, 132, 32, 10, 1]

private theorem o198from77_QtInv :
    (codeMat 215 : Mat3).transpose⁻¹ = (codeMat 342 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 215 : Mat3).transpose * (codeMat 342 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o198W_le_action_77 :
    o198W_mono ≤ actionW (codeMat 122) (codeMat 215) o77W_T := by
  apply o198from77_spanCodes_le_of_gens [326, 132, 32, 10, 1]
    (actionW (codeMat 122) (codeMat 215) o77W_T)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 164 ∈ o77W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 164 (by decide)
    have hact : actionA (codeMat 122) (codeMat 215) (codeMat 164) = codeMat 326 := by
      unfold actionA
      rw [o198from77_QtInv]
      show (codeMat 122 : Mat3).transpose * codeMat 164 * (codeMat 342 : Mat3).transpose = codeMat 326
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o198from77_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 447 ∈ o77W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 447 (by decide)
    have hact : actionA (codeMat 122) (codeMat 215) (codeMat 447) = codeMat 132 := by
      unfold actionA
      rw [o198from77_QtInv]
      show (codeMat 122 : Mat3).transpose * codeMat 447 * (codeMat 342 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o198from77_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ o77W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 122) (codeMat 215) (codeMat 1) = codeMat 32 := by
      unfold actionA
      rw [o198from77_QtInv]
      show (codeMat 122 : Mat3).transpose * codeMat 1 * (codeMat 342 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o198from77_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 453 ∈ o77W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 453 (by decide)
    have hact : actionA (codeMat 122) (codeMat 215) (codeMat 453) = codeMat 10 := by
      unfold actionA
      rw [o198from77_QtInv]
      show (codeMat 122 : Mat3).transpose * codeMat 453 * (codeMat 342 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o198from77_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 320 ∈ o77W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 320 (by decide)
    have hact : actionA (codeMat 122) (codeMat 215) (codeMat 320) = codeMat 1 := by
      unfold actionA
      rw [o198from77_QtInv]
      show (codeMat 122 : Mat3).transpose * codeMat 320 * (codeMat 342 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o198from77_codeMat_mem_actionW_of_witness hw hact

theorem orbit198_lb15_mono : QuotientRankAtLeast o198W_mono 15 := by
  have hP : Invertible (codeMat 122 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 215 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 122) (codeMat 215) o77W_T) 15 :=
    @quotientRankAtLeast_action (codeMat 122) (codeMat 215) hP hQ o77W_T 15
      o77W_T_lb
  exact quotientRankAtLeast_mono o198W_le_action_77 hAct

end QiushiMatmul
