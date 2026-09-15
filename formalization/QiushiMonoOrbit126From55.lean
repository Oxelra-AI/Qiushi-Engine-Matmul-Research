import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiStep99Orbit55Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem o126from55_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o126from55_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 126, basis [256, 96, 12, 2, 1]. -/
def o126W_mono : Submodule F2 Mat3 := spanCodes [256, 96, 12, 2, 1]

private theorem o126from55_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o126W_le_action_55 :
    o126W_mono ≤ actionW (codeMat 161) (codeMat 266) o55W := by
  apply o126from55_spanCodes_le_of_gens [256, 96, 12, 2, 1]
    (actionW (codeMat 161) (codeMat 266) o55W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 32 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 32) = codeMat 256 := by
      unfold actionA
      rw [o126from55_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 32 * (codeMat 266 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o126from55_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 272 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 272 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 272) = codeMat 96 := by
      unfold actionA
      rw [o126from55_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 272 * (codeMat 266 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o126from55_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 132 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 132 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 132) = codeMat 12 := by
      unfold actionA
      rw [o126from55_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 132 * (codeMat 266 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o126from55_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 1) = codeMat 2 := by
      unfold actionA
      rw [o126from55_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o126from55_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [o126from55_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o126from55_codeMat_mem_actionW_of_witness hw hact

theorem orbit126_lb14_mono : QuotientRankAtLeast o126W_mono 14 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 266) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 266) hP hQ o55W 14
      step99_orbit55_lb14_unconditional
  exact quotientRankAtLeast_mono o126W_le_action_55 hAct

end QiushiMatmul
