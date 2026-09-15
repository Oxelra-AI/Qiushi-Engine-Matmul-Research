import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiStep107Orbit373Extraction

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem o446from373_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o446from373_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 446, basis [304, 160, 1]. -/
def o446W_mono : Submodule F2 Mat3 := spanCodes [304, 160, 1]

private theorem o446from373_QtInv :
    (codeMat 165 : Mat3).transpose⁻¹ = (codeMat 163 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 165 : Mat3).transpose * (codeMat 163 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o446W_le_action_373 :
    o446W_mono ≤ actionW (codeMat 161) (codeMat 165) o373W := by
  apply o446from373_spanCodes_le_of_gens [304, 160, 1]
    (actionW (codeMat 161) (codeMat 165) o373W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    have hw : codeMat 472 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 472 (by decide)
    have hact : actionA (codeMat 161) (codeMat 165) (codeMat 472) = codeMat 304 := by
      unfold actionA
      rw [o446from373_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 472 * (codeMat 163 : Mat3).transpose = codeMat 304
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o446from373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 224 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 224 (by decide)
    have hact : actionA (codeMat 161) (codeMat 165) (codeMat 224) = codeMat 160 := by
      unfold actionA
      rw [o446from373_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 224 * (codeMat 163 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o446from373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 165) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [o446from373_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 163 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o446from373_codeMat_mem_actionW_of_witness hw hact

theorem orbit446_lb17_mono : QuotientRankAtLeast o446W_mono 17 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 165 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 165) o373W) 17 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 165) hP hQ o373W 17
      step107_orbit373_lb17
  exact quotientRankAtLeast_mono o446W_le_action_373 hAct

end QiushiMatmul
