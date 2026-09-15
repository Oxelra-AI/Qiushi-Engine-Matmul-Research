import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiStep99Orbit55Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem o137from55_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o137from55_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 137, basis [272, 80, 32, 2, 1]. -/
def o137W_mono : Submodule F2 Mat3 := spanCodes [272, 80, 32, 2, 1]

private theorem o137from55_QtInv :
    (codeMat 313 : Mat3).transpose⁻¹ = (codeMat 313 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 313 : Mat3).transpose * (codeMat 313 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o137W_le_action_55 :
    o137W_mono ≤ actionW (codeMat 425) (codeMat 313) o55W := by
  apply o137from55_spanCodes_le_of_gens [272, 80, 32, 2, 1]
    (actionW (codeMat 425) (codeMat 313) o55W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 164 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 164 (by decide)
    have hact : actionA (codeMat 425) (codeMat 313) (codeMat 164) = codeMat 272 := by
      unfold actionA
      rw [o137from55_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 164 * (codeMat 313 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o137from55_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 137 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 137 (by decide)
    have hact : actionA (codeMat 425) (codeMat 313) (codeMat 137) = codeMat 80 := by
      unfold actionA
      rw [o137from55_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 137 * (codeMat 313 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o137from55_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 438 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 438 (by decide)
    have hact : actionA (codeMat 425) (codeMat 313) (codeMat 438) = codeMat 32 := by
      unfold actionA
      rw [o137from55_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 438 * (codeMat 313 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o137from55_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 425) (codeMat 313) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [o137from55_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 2 * (codeMat 313 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o137from55_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 425) (codeMat 313) (codeMat 3) = codeMat 1 := by
      unfold actionA
      rw [o137from55_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 3 * (codeMat 313 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o137from55_codeMat_mem_actionW_of_witness hw hact

theorem orbit137_lb14_mono : QuotientRankAtLeast o137W_mono 14 := by
  have hP : Invertible (codeMat 425 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 313 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 425) (codeMat 313) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 425) (codeMat 313) hP hQ o55W 14
      step99_orbit55_lb14_unconditional
  exact quotientRankAtLeast_mono o137W_le_action_55 hAct

end QiushiMatmul
