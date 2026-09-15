import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiStep99Orbit65Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem o174from65_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o174from65_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 174, basis [260, 160, 20, 10, 1]. -/
def o174W_mono : Submodule F2 Mat3 := spanCodes [260, 160, 20, 10, 1]

private theorem o174from65_QtInv :
    (codeMat 401 : Mat3).transpose⁻¹ = (codeMat 401 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 401 : Mat3).transpose * (codeMat 401 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o174W_le_action_65 :
    o174W_mono ≤ actionW (codeMat 305) (codeMat 401) o65W := by
  apply o174from65_spanCodes_le_of_gens [260, 160, 20, 10, 1]
    (actionW (codeMat 305) (codeMat 401) o65W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 260 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 260 (by decide)
    have hact : actionA (codeMat 305) (codeMat 401) (codeMat 260) = codeMat 260 := by
      unfold actionA
      rw [o174from65_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 260 * (codeMat 401 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o174from65_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 305) (codeMat 401) (codeMat 160) = codeMat 160 := by
      unfold actionA
      rw [o174from65_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 160 * (codeMat 401 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o174from65_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 436 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 436 (by decide)
    have hact : actionA (codeMat 305) (codeMat 401) (codeMat 436) = codeMat 20 := by
      unfold actionA
      rw [o174from65_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 436 * (codeMat 401 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o174from65_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 78 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 78 (by decide)
    have hact : actionA (codeMat 305) (codeMat 401) (codeMat 78) = codeMat 10 := by
      unfold actionA
      rw [o174from65_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 78 * (codeMat 401 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o174from65_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 305) (codeMat 401) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [o174from65_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 1 * (codeMat 401 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o174from65_codeMat_mem_actionW_of_witness hw hact

theorem orbit174_lb15_mono : QuotientRankAtLeast o174W_mono 15 := by
  have hP : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 305) (codeMat 401) o65W) 15 :=
    @quotientRankAtLeast_action (codeMat 305) (codeMat 401) hP hQ o65W 15
      step99_orbit65_lb15_unconditional
  exact quotientRankAtLeast_mono o174W_le_action_65 hAct

end QiushiMatmul
