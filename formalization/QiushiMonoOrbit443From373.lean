import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiStep107Orbit373Extraction

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem o443from373_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o443from373_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 443, basis [266, 20, 1]. -/
def o443W_mono : Submodule F2 Mat3 := spanCodes [266, 20, 1]

private theorem o443from373_QtInv :
    (codeMat 309 : Mat3).transpose⁻¹ = (codeMat 309 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 309 : Mat3).transpose * (codeMat 309 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o443W_le_action_373 :
    o443W_mono ≤ actionW (codeMat 345) (codeMat 309) o373W := by
  apply o443from373_spanCodes_le_of_gens [266, 20, 1]
    (actionW (codeMat 345) (codeMat 309) o373W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    have hw : codeMat 460 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 460 (by decide)
    have hact : actionA (codeMat 345) (codeMat 309) (codeMat 460) = codeMat 266 := by
      unfold actionA
      rw [o443from373_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 460 * (codeMat 309 : Mat3).transpose = codeMat 266
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o443from373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 21 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 21 (by decide)
    have hact : actionA (codeMat 345) (codeMat 309) (codeMat 21) = codeMat 20 := by
      unfold actionA
      rw [o443from373_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 21 * (codeMat 309 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o443from373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ o373W :=
      spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1] 1 (by decide)
    have hact : actionA (codeMat 345) (codeMat 309) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [o443from373_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 1 * (codeMat 309 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o443from373_codeMat_mem_actionW_of_witness hw hact

theorem orbit443_lb17_mono : QuotientRankAtLeast o443W_mono 17 := by
  have hP : Invertible (codeMat 345 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 309 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 345) (codeMat 309) o373W) 17 :=
    @quotientRankAtLeast_action (codeMat 345) (codeMat 309) hP hQ o373W 17
      step107_orbit373_lb17
  exact quotientRankAtLeast_mono o443W_le_action_373 hAct

end QiushiMatmul
