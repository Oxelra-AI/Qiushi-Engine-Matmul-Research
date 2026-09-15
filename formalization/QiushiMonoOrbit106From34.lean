import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiStep99Orbit34Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem o106from34_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o106from34_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 106, basis [256, 68, 8, 2, 1]. -/
def o106W_mono : Submodule F2 Mat3 := spanCodes [256, 68, 8, 2, 1]

private theorem o106from34_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o106W_le_action_34 :
    o106W_mono ≤ actionW (codeMat 273) (codeMat 273) o34W := by
  apply o106from34_spanCodes_le_of_gens [256, 68, 8, 2, 1]
    (actionW (codeMat 273) (codeMat 273) o34W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 256 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 256) = codeMat 256 := by
      unfold actionA
      rw [o106from34_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 256 * (codeMat 273 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o106from34_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 68 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 68 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 68) = codeMat 68 := by
      unfold actionA
      rw [o106from34_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 68 * (codeMat 273 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o106from34_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [o106from34_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 273 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o106from34_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [o106from34_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o106from34_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [o106from34_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o106from34_codeMat_mem_actionW_of_witness hw hact

theorem orbit106_lb14_mono : QuotientRankAtLeast o106W_mono 14 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 273) o34W) 14 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 273) hP hQ o34W 14
      step99_orbit34_lb14_unconditional
  exact quotientRankAtLeast_mono o106W_le_action_34 hAct

end QiushiMatmul
