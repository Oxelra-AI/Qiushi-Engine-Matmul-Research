import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiStep99Orbit150Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem o288from150_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o288from150_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 288, basis [256, 20, 10, 1]. -/
def o288W_mono : Submodule F2 Mat3 := spanCodes [256, 20, 10, 1]

private theorem o288from150_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o288W_le_action_150 :
    o288W_mono ≤ actionW (codeMat 161) (codeMat 161) o150W := by
  apply o288from150_spanCodes_le_of_gens [256, 20, 10, 1]
    (actionW (codeMat 161) (codeMat 161) o150W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    have hw : codeMat 16 ∈ o150W :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 16) = codeMat 256 := by
      unfold actionA
      rw [o288from150_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 16 * (codeMat 161 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o288from150_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 258 ∈ o150W :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 16, 10, 1] 258 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 258) = codeMat 20 := by
      unfold actionA
      rw [o288from150_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 258 * (codeMat 161 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o288from150_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ o150W :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 16, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 68) = codeMat 10 := by
      unfold actionA
      rw [o288from150_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 68 * (codeMat 161 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o288from150_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o150W :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [o288from150_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o288from150_codeMat_mem_actionW_of_witness hw hact

theorem orbit288_lb16_mono : QuotientRankAtLeast o288W_mono 16 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 161) o150W) 16 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 161) hP hQ o150W 16
      step99_orbit150_lb16_unconditional
  exact quotientRankAtLeast_mono o288W_le_action_150 hAct

end QiushiMatmul
