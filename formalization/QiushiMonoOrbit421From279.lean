import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiStep104Orbit279Split

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem o421from279_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o421from279_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 421, basis [84, 10, 1]. -/
def o421W_mono : Submodule F2 Mat3 := spanCodes [84, 10, 1]

private theorem o421from279_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o421W_le_action_279 :
    o421W_mono ≤ actionW (codeMat 273) (codeMat 273) o279W := by
  apply o421from279_spanCodes_le_of_gens [84, 10, 1]
    (actionW (codeMat 273) (codeMat 273) o279W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    have hw : codeMat 84 ∈ o279W :=
      spanContainsCodeCore_implies_mem_spanCodes [68, 16, 10, 1] 84 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 84) = codeMat 84 := by
      unfold actionA
      rw [o421from279_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 84 * (codeMat 273 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o421from279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 10 ∈ o279W :=
      spanContainsCodeCore_implies_mem_spanCodes [68, 16, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [o421from279_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 10 * (codeMat 273 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o421from279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ o279W :=
      spanContainsCodeCore_implies_mem_spanCodes [68, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [o421from279_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o421from279_codeMat_mem_actionW_of_witness hw hact

theorem orbit421_lb17_mono : QuotientRankAtLeast o421W_mono 17 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 273) o279W) 17 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 273) hP hQ o279W 17
      step104_orbit279_lb17
  exact quotientRankAtLeast_mono o421W_le_action_279 hAct

end QiushiMatmul
