import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiStep99Orbit196Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private def o196W_T : Submodule F2 Mat3 := spanCodes [306, 128, 96, 10, 1]

private theorem o196W_T_lb : QuotientRankAtLeast o196W_T 16 := by
  have ht := quotientRankAtLeast_transpose step99_orbit196_lb16_unconditional
  have hle : o196W_T ≤ transposeW o196W := by
    unfold o196W_T transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4
    · subst h0
      show codeMat 306 ∈ Submodule.map transposeLinearMap o196W
      exact ⟨codeMat 408, spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 408 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 128 ∈ Submodule.map transposeLinearMap o196W
      exact ⟨codeMat 32, spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 32 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 96 ∈ Submodule.map transposeLinearMap o196W
      exact ⟨codeMat 132, spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 132 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 10 ∈ Submodule.map transposeLinearMap o196W
      exact ⟨codeMat 10, spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 10 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 1 ∈ Submodule.map transposeLinearMap o196W
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem o310from196_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o310from196_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 310, basis [304, 96, 10, 1]. -/
def o310W_mono : Submodule F2 Mat3 := spanCodes [304, 96, 10, 1]

private theorem o310from196_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = (codeMat 275 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * (codeMat 275 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o310W_le_action_196 :
    o310W_mono ≤ actionW (codeMat 273) (codeMat 275) o196W_T := by
  apply o310from196_spanCodes_le_of_gens [304, 96, 10, 1]
    (actionW (codeMat 273) (codeMat 275) o196W_T)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    have hw : codeMat 312 ∈ o196W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 128, 96, 10, 1] 312 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 312) = codeMat 304 := by
      unfold actionA
      rw [o310from196_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 312 * (codeMat 275 : Mat3).transpose = codeMat 304
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o310from196_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 96 ∈ o196W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 128, 96, 10, 1] 96 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 96) = codeMat 96 := by
      unfold actionA
      rw [o310from196_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 96 * (codeMat 275 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o310from196_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 11 ∈ o196W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 128, 96, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 11) = codeMat 10 := by
      unfold actionA
      rw [o310from196_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 11 * (codeMat 275 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o310from196_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o196W_T :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 128, 96, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [o310from196_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 275 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o310from196_codeMat_mem_actionW_of_witness hw hact

theorem orbit310_lb16_mono : QuotientRankAtLeast o310W_mono 16 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 275) o196W_T) 16 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 275) hP hQ o196W_T 16
      o196W_T_lb
  exact quotientRankAtLeast_mono o310W_le_action_196 hAct

end QiushiMatmul
