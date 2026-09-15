import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiStep99Orbit55Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem o121from55_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o121from55_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 121, basis [384, 32, 12, 2, 1]. -/
def o121W_mono : Submodule F2 Mat3 := spanCodes [384, 32, 12, 2, 1]

private theorem o121from55_QtInv :
    (codeMat 279 : Mat3).transpose⁻¹ = (codeMat 279 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 279 : Mat3).transpose * (codeMat 279 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o121W_le_action_55 :
    o121W_mono ≤ actionW (codeMat 409) (codeMat 279) o55W := by
  apply o121from55_spanCodes_le_of_gens [384, 32, 12, 2, 1]
    (actionW (codeMat 409) (codeMat 279) o55W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 438 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 438 (by decide)
    have hact : actionA (codeMat 409) (codeMat 279) (codeMat 438) = codeMat 384 := by
      unfold actionA
      rw [o121from55_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 438 * (codeMat 279 : Mat3).transpose = codeMat 384
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o121from55_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 45 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 45 (by decide)
    have hact : actionA (codeMat 409) (codeMat 279) (codeMat 45) = codeMat 32 := by
      unfold actionA
      rw [o121from55_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 45 * (codeMat 279 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o121from55_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 12 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 12 (by decide)
    have hact : actionA (codeMat 409) (codeMat 279) (codeMat 12) = codeMat 12 := by
      unfold actionA
      rw [o121from55_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 12 * (codeMat 279 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o121from55_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 3 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 409) (codeMat 279) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [o121from55_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 3 * (codeMat 279 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o121from55_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 409) (codeMat 279) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [o121from55_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 1 * (codeMat 279 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o121from55_codeMat_mem_actionW_of_witness hw hact

theorem orbit121_lb14_mono : QuotientRankAtLeast o121W_mono 14 := by
  have hP : Invertible (codeMat 409 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 279 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 409) (codeMat 279) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 409) (codeMat 279) hP hQ o55W 14
      step99_orbit55_lb14_unconditional
  exact quotientRankAtLeast_mono o121W_le_action_55 hAct

end QiushiMatmul
