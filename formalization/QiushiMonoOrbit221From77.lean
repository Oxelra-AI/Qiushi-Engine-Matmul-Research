import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiStep99Orbit77Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem o221from77_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o221from77_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 221, basis [330, 196, 36, 16, 1]. -/
def o221W_mono : Submodule F2 Mat3 := spanCodes [330, 196, 36, 16, 1]

private theorem o221from77_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o221W_le_action_77 :
    o221W_mono ≤ actionW (codeMat 114) (codeMat 266) o77W := by
  apply o221from77_spanCodes_le_of_gens [330, 196, 36, 16, 1]
    (actionW (codeMat 114) (codeMat 266) o77W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 116 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 116 (by decide)
    have hact : actionA (codeMat 114) (codeMat 266) (codeMat 116) = codeMat 330 := by
      unfold actionA
      rw [o221from77_QtInv]
      show (codeMat 114 : Mat3).transpose * codeMat 116 * (codeMat 266 : Mat3).transpose = codeMat 330
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o221from77_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 283 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 283 (by decide)
    have hact : actionA (codeMat 114) (codeMat 266) (codeMat 283) = codeMat 196 := by
      unfold actionA
      rw [o221from77_QtInv]
      show (codeMat 114 : Mat3).transpose * codeMat 283 * (codeMat 266 : Mat3).transpose = codeMat 196
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o221from77_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 260 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 260 (by decide)
    have hact : actionA (codeMat 114) (codeMat 266) (codeMat 260) = codeMat 36 := by
      unfold actionA
      rw [o221from77_QtInv]
      show (codeMat 114 : Mat3).transpose * codeMat 260 * (codeMat 266 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o221from77_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 114) (codeMat 266) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [o221from77_QtInv]
      show (codeMat 114 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o221from77_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 128 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 114) (codeMat 266) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [o221from77_QtInv]
      show (codeMat 114 : Mat3).transpose * codeMat 128 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o221from77_codeMat_mem_actionW_of_witness hw hact

theorem orbit221_lb15_mono : QuotientRankAtLeast o221W_mono 15 := by
  have hP : Invertible (codeMat 114 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 114) (codeMat 266) o77W) 15 :=
    @quotientRankAtLeast_action (codeMat 114) (codeMat 266) hP hQ o77W 15
      step99_orbit77_lb15_unconditional
  exact quotientRankAtLeast_mono o221W_le_action_77 hAct

end QiushiMatmul
