import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiStep99Orbit150Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem o319from150_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o319from150_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 319, basis [292, 160, 10, 1]. -/
def o319W_mono : Submodule F2 Mat3 := spanCodes [292, 160, 10, 1]

private theorem o319from150_QtInv :
    (codeMat 183 : Mat3).transpose⁻¹ = (codeMat 419 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 183 : Mat3).transpose * (codeMat 419 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o319W_le_action_150 :
    o319W_mono ≤ actionW (codeMat 305) (codeMat 183) o150W := by
  apply o319from150_spanCodes_le_of_gens [292, 160, 10, 1]
    (actionW (codeMat 305) (codeMat 183) o150W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    have hw : codeMat 27 ∈ o150W :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 16, 10, 1] 27 (by decide)
    have hact : actionA (codeMat 305) (codeMat 183) (codeMat 27) = codeMat 292 := by
      unfold actionA
      rw [o319from150_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 27 * (codeMat 419 : Mat3).transpose = codeMat 292
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o319from150_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 280 ∈ o150W :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 16, 10, 1] 280 (by decide)
    have hact : actionA (codeMat 305) (codeMat 183) (codeMat 280) = codeMat 160 := by
      unfold actionA
      rw [o319from150_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 280 * (codeMat 419 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o319from150_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 79 ∈ o150W :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 16, 10, 1] 79 (by decide)
    have hact : actionA (codeMat 305) (codeMat 183) (codeMat 79) = codeMat 10 := by
      unfold actionA
      rw [o319from150_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 79 * (codeMat 419 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o319from150_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o150W :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 305) (codeMat 183) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [o319from150_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 1 * (codeMat 419 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o319from150_codeMat_mem_actionW_of_witness hw hact

theorem orbit319_lb16_mono : QuotientRankAtLeast o319W_mono 16 := by
  have hP : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 183 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 305) (codeMat 183) o150W) 16 :=
    @quotientRankAtLeast_action (codeMat 305) (codeMat 183) hP hQ o150W 16
      step99_orbit150_lb16_unconditional
  exact quotientRankAtLeast_mono o319W_le_action_150 hAct

end QiushiMatmul
