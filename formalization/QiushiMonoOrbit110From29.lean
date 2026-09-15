import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiOrbit29FP

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem o110from29_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o110from29_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 110, basis [132, 96, 8, 2, 1]. -/
def o110W_mono : Submodule F2 Mat3 := spanCodes [132, 96, 8, 2, 1]

private theorem o110from29_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o110W_le_action_29 :
    o110W_mono ≤ actionW (codeMat 266) (codeMat 273) orbit29W := by
  apply o110from29_spanCodes_le_of_gens [132, 96, 8, 2, 1]
    (actionW (codeMat 266) (codeMat 273) orbit29W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 160 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 160 (by decide)
    have hact : actionA (codeMat 266) (codeMat 273) (codeMat 160) = codeMat 132 := by
      unfold actionA
      rw [o110from29_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 160 * (codeMat 273 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o110from29_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 68 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 68 (by decide)
    have hact : actionA (codeMat 266) (codeMat 273) (codeMat 68) = codeMat 96 := by
      unfold actionA
      rw [o110from29_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 68 * (codeMat 273 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o110from29_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 273) (codeMat 1) = codeMat 8 := by
      unfold actionA
      rw [o110from29_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o110from29_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 16 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 273) (codeMat 16) = codeMat 2 := by
      unfold actionA
      rw [o110from29_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 273 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o110from29_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 273) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [o110from29_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o110from29_codeMat_mem_actionW_of_witness hw hact

theorem orbit110_lb15_mono : QuotientRankAtLeast o110W_mono 15 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 273) orbit29W) 15 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 273) hP hQ orbit29W 15
      orbit29_lb15
  exact quotientRankAtLeast_mono o110W_le_action_29 hAct

end QiushiMatmul
