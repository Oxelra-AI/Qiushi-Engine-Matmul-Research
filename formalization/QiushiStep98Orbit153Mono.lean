import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiStep99Orbit65Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem step98o153_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step98o153_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 153, canonical representative. -/
def o153W : Submodule F2 Mat3 := spanCodes [256, 96, 16, 10, 1]

private theorem step98o153_QtInv :
    (codeMat 225 : Mat3).transpose⁻¹ = (codeMat 169 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 225 : Mat3).transpose * (codeMat 169 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step98o153_targetSpan_le_action :
    o153W ≤ actionW (codeMat 99) (codeMat 225) o65W := by
  apply step98o153_spanCodes_le_of_gens [256, 96, 16, 10, 1]
    (actionW (codeMat 99) (codeMat 225) o65W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 16 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 99) (codeMat 225) (codeMat 16) = codeMat 256 := by
      unfold actionA
      rw [step98o153_QtInv]
      show (codeMat 99 : Mat3).transpose * codeMat 16 * (codeMat 169 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step98o153_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 170 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 170 (by decide)
    have hact : actionA (codeMat 99) (codeMat 225) (codeMat 170) = codeMat 96 := by
      unfold actionA
      rw [step98o153_QtInv]
      show (codeMat 99 : Mat3).transpose * codeMat 170 * (codeMat 169 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step98o153_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 260 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 260 (by decide)
    have hact : actionA (codeMat 99) (codeMat 225) (codeMat 260) = codeMat 16 := by
      unfold actionA
      rw [step98o153_QtInv]
      show (codeMat 99 : Mat3).transpose * codeMat 260 * (codeMat 169 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step98o153_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 69 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 69 (by decide)
    have hact : actionA (codeMat 99) (codeMat 225) (codeMat 69) = codeMat 10 := by
      unfold actionA
      rw [step98o153_QtInv]
      show (codeMat 99 : Mat3).transpose * codeMat 69 * (codeMat 169 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step98o153_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 320 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 320 (by decide)
    have hact : actionA (codeMat 99) (codeMat 225) (codeMat 320) = codeMat 1 := by
      unfold actionA
      rw [step98o153_QtInv]
      show (codeMat 99 : Mat3).transpose * codeMat 320 * (codeMat 169 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step98o153_codeMat_mem_actionW_of_witness hw hact

/-- Orbit 153 lower bound 15, obtained by monotonicity from orbit 65 under the
explicit `GL₃(F₂) × GL₃(F₂)` action witness `(P,Q)=(99,225)`. -/
theorem step98_orbit153_lb15_unconditional :
    QuotientRankAtLeast o153W 15 := by
  have hP : Invertible (codeMat 99 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 99) (codeMat 225) o65W) 15 :=
    @quotientRankAtLeast_action (codeMat 99) (codeMat 225) hP hQ o65W 15
      step99_orbit65_lb15_unconditional
  exact quotientRankAtLeast_mono step98o153_targetSpan_le_action hAct

end QiushiMatmul
