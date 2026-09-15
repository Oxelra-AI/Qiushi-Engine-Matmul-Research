import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiStep81Qdim2Generated

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem o74from17_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o74from17_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 74, basis [324, 192, 32, 20, 10, 1]. -/
def o74W_mono : Submodule F2 Mat3 := spanCodes [324, 192, 32, 20, 10, 1]

private theorem o74from17_QtInv :
    (codeMat 282 : Mat3).transpose⁻¹ = (codeMat 267 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 282 : Mat3).transpose * (codeMat 267 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o74W_le_action_17 :
    o74W_mono ≤ actionW (codeMat 84) (codeMat 282) step81o17s4Wspan := by
  apply o74from17_spanCodes_le_of_gens [324, 192, 32, 20, 10, 1]
    (actionW (codeMat 84) (codeMat 282) step81o17s4Wspan)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 262 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 262 (by decide)
    have hact : actionA (codeMat 84) (codeMat 282) (codeMat 262) = codeMat 324 := by
      unfold actionA
      rw [o74from17_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 262 * (codeMat 267 : Mat3).transpose = codeMat 324
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o74from17_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 282) (codeMat 1) = codeMat 192 := by
      unfold actionA
      rw [o74from17_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 267 : Mat3).transpose = codeMat 192
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o74from17_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 32 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 84) (codeMat 282) (codeMat 32) = codeMat 32 := by
      unfold actionA
      rw [o74from17_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 32 * (codeMat 267 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o74from17_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 280 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 280 (by decide)
    have hact : actionA (codeMat 84) (codeMat 282) (codeMat 280) = codeMat 20 := by
      unfold actionA
      rw [o74from17_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 280 * (codeMat 267 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o74from17_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 208 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 208 (by decide)
    have hact : actionA (codeMat 84) (codeMat 282) (codeMat 208) = codeMat 10 := by
      unfold actionA
      rw [o74from17_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 208 * (codeMat 267 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o74from17_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 282) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [o74from17_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 267 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o74from17_codeMat_mem_actionW_of_witness hw hact

theorem orbit74_lb14_mono : QuotientRankAtLeast o74W_mono 14 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 282 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 282) step81o17s4Wspan) 14 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 282) hP hQ step81o17s4Wspan 14
      step81o17s4Span_lb
  exact quotientRankAtLeast_mono o74W_le_action_17 hAct

end QiushiMatmul
