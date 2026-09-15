import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiBranch262Extraction

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem o414from262_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o414from262_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 414, basis [272, 4, 2]. Reducer sink: affineHyperplane0. -/
def o414W_mono : Submodule F2 Mat3 := spanCodes [272, 4, 2]

-- P=161, Q=84.
private theorem o414from262_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o414W_le_action_262 :
    o414W_mono ≤ actionW (codeMat 161) (codeMat 84) o262W := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  apply o414from262_spanCodes_le_of_gens [272, 4, 2]
    (actionW (codeMat 161) (codeMat 84) o262W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · -- Generator 272: preimage 136 = 132 XOR 12
    subst h0
    have hw : codeMat 136 ∈ o262W :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 12, 2, 1] 136 (by decide)
    have hact : actionA (codeMat 161) (codeMat 84) (codeMat 136) = codeMat 272 := by
      unfold actionA
      rw [o414from262_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 136 * (codeMat 84 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o414from262_codeMat_mem_actionW_of_witness hw hact
  · -- Generator 4: preimage 1
    subst h1
    have hw : codeMat 1 ∈ o262W :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 84) (codeMat 1) = codeMat 4 := by
      unfold actionA
      rw [o414from262_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 84 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o414from262_codeMat_mem_actionW_of_witness hw hact
  · -- Generator 2: preimage 2
    subst h2
    have hw : codeMat 2 ∈ o262W :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 84) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [o414from262_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 84 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o414from262_codeMat_mem_actionW_of_witness hw hact

/-- Orbit 414 quotient rank ≥17 by transport monotonicity from orbit 262. -/
theorem orbit414_lb17_mono : QuotientRankAtLeast o414W_mono 17 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 84) o262W) 17 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 84) hP hQ o262W 17
      step113_orbit262_lb17
  exact quotientRankAtLeast_mono o414W_le_action_262 hAct

end QiushiMatmul
