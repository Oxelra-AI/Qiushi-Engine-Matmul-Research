import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiStep99Orbit65Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem o176from65_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o176from65_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 176, basis [128, 68, 32, 10, 1]. -/
def o176W_mono : Submodule F2 Mat3 := spanCodes [128, 68, 32, 10, 1]

private theorem o176from65_QtInv :
    (codeMat 396 : Mat3).transpose⁻¹ = (codeMat 106 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 396 : Mat3).transpose * (codeMat 106 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o176W_le_action_65 :
    o176W_mono ≤ actionW (codeMat 142) (codeMat 396) o65W := by
  apply o176from65_spanCodes_le_of_gens [128, 68, 32, 10, 1]
    (actionW (codeMat 142) (codeMat 396) o65W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 260 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 260 (by decide)
    have hact : actionA (codeMat 142) (codeMat 396) (codeMat 260) = codeMat 128 := by
      unfold actionA
      rw [o176from65_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 260 * (codeMat 106 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o176from65_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 170 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 170 (by decide)
    have hact : actionA (codeMat 142) (codeMat 396) (codeMat 170) = codeMat 68 := by
      unfold actionA
      rw [o176from65_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 170 * (codeMat 106 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o176from65_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 320 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 320 (by decide)
    have hact : actionA (codeMat 142) (codeMat 396) (codeMat 320) = codeMat 32 := by
      unfold actionA
      rw [o176from65_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 320 * (codeMat 106 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o176from65_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 160 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 142) (codeMat 396) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [o176from65_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 160 * (codeMat 106 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o176from65_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 16 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 142) (codeMat 396) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [o176from65_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 16 * (codeMat 106 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o176from65_codeMat_mem_actionW_of_witness hw hact

theorem orbit176_lb15_mono : QuotientRankAtLeast o176W_mono 15 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 396 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 396) o65W) 15 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 396) hP hQ o65W 15
      step99_orbit65_lb15_unconditional
  exact quotientRankAtLeast_mono o176W_le_action_65 hAct

end QiushiMatmul
