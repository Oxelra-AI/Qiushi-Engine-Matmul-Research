import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiStep107Orbit373Extraction

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem o444from373_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o444from373_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 444, basis [160, 84, 1]. -/
def o444W_mono : Submodule F2 Mat3 := spanCodes [160, 84, 1]

private theorem o444from373_QtInv :
    (codeMat 403 : Mat3).transpose⁻¹ = (codeMat 403 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 403 : Mat3).transpose * (codeMat 403 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o444W_le_action_373 :
    o444W_mono ≤ actionW (codeMat 161) (codeMat 403) o373W := by
  apply o444from373_spanCodes_le_of_gens [160, 84, 1]
    (actionW (codeMat 161) (codeMat 403) o373W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    have hw : codeMat 312 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 312 (by decide)
    have hact : actionA (codeMat 161) (codeMat 403) (codeMat 312) = codeMat 160 := by
      unfold actionA
      rw [o444from373_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 312 * (codeMat 403 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o444from373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 460 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 460 (by decide)
    have hact : actionA (codeMat 161) (codeMat 403) (codeMat 460) = codeMat 84 := by
      unfold actionA
      rw [o444from373_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 460 * (codeMat 403 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o444from373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 403) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [o444from373_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 403 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o444from373_codeMat_mem_actionW_of_witness hw hact

theorem orbit444_lb17_mono : QuotientRankAtLeast o444W_mono 17 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 403 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 403) o373W) 17 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 403) hP hQ o373W 17
      step107_orbit373_lb17
  exact quotientRankAtLeast_mono o444W_le_action_373 hAct

end QiushiMatmul
