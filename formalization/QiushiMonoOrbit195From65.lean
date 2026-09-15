import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiStep99Orbit65Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem o195from65_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o195from65_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 195, basis [274, 132, 32, 10, 1]. -/
def o195W_mono : Submodule F2 Mat3 := spanCodes [274, 132, 32, 10, 1]

private theorem o195from65_QtInv :
    (codeMat 412 : Mat3).transpose⁻¹ = (codeMat 111 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 412 : Mat3).transpose * (codeMat 111 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o195W_le_action_65 :
    o195W_mono ≤ actionW (codeMat 142) (codeMat 412) o65W := by
  apply o195from65_spanCodes_le_of_gens [274, 132, 32, 10, 1]
    (actionW (codeMat 142) (codeMat 412) o65W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 245 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 245 (by decide)
    have hact : actionA (codeMat 142) (codeMat 412) (codeMat 245) = codeMat 274 := by
      unfold actionA
      rw [o195from65_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 245 * (codeMat 111 : Mat3).transpose = codeMat 274
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o195from65_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 430 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 430 (by decide)
    have hact : actionA (codeMat 142) (codeMat 412) (codeMat 430) = codeMat 132 := by
      unfold actionA
      rw [o195from65_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 430 * (codeMat 111 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o195from65_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 320 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 320 (by decide)
    have hact : actionA (codeMat 142) (codeMat 412) (codeMat 320) = codeMat 32 := by
      unfold actionA
      rw [o195from65_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 320 * (codeMat 111 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o195from65_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 176 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 176 (by decide)
    have hact : actionA (codeMat 142) (codeMat 412) (codeMat 176) = codeMat 10 := by
      unfold actionA
      rw [o195from65_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 176 * (codeMat 111 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o195from65_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 16 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 142) (codeMat 412) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [o195from65_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 16 * (codeMat 111 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o195from65_codeMat_mem_actionW_of_witness hw hact

theorem orbit195_lb15_mono : QuotientRankAtLeast o195W_mono 15 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 412 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 412) o65W) 15 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 412) hP hQ o65W 15
      step99_orbit65_lb15_unconditional
  exact quotientRankAtLeast_mono o195W_le_action_65 hAct

end QiushiMatmul
