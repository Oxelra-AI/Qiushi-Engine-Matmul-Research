import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit16Consumer
import QiushiFlattenSeeds

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc16_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc16_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc16s0_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc16s0_contain :
    (o16SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 84) (codeMat 140) flatW_3 := by
  change spanCodes [256, 132, 64, 32, 16, 12, 2, 1] ≤ actionW (codeMat 84) (codeMat 140) flatW_3
  apply step109wc16_spanCodes_le_of_gens [256, 132, 64, 32, 16, 12, 2, 1]
    (actionW (codeMat 84) (codeMat 140) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 1 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step109wc16s0_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc16_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 68 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 68 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 68) = codeMat 132 := by
      unfold actionA
      rw [step109wc16s0_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 68 * (codeMat 98 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc16_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 2) = codeMat 64 := by
      unfold actionA
      rw [step109wc16s0_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 98 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc16_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc16s0_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc16_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 32 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 32) = codeMat 16 := by
      unfold actionA
      rw [step109wc16s0_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 32 * (codeMat 98 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc16_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 80 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 80 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 80) = codeMat 12 := by
      unfold actionA
      rw [step109wc16s0_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 80 * (codeMat 98 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc16_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 256) = codeMat 2 := by
      unfold actionA
      rw [step109wc16s0_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 98 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc16_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 128 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc16s0_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc16_codeMat_mem_actionW_of_witness hw hact

theorem step109wc16s0Dispatch :
    QuotientRankAtLeast (o16SourceU_wc ⟨0, by omega⟩) 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 140) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 140) hP hQ flatW_3 9
      flatSeed_3
  exact quotientRankAtLeast_mono step109wc16s0_contain hAct


private theorem step109wc16s1_QtInv :
    (codeMat 92 : Mat3).transpose⁻¹ = (codeMat 116 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 92 : Mat3).transpose * (codeMat 116 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc16s1_contain :
    (o16SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 84) (codeMat 92) flatW_3 := by
  change spanCodes [256, 128, 68, 32, 20, 12, 2, 1] ≤ actionW (codeMat 84) (codeMat 92) flatW_3
  apply step109wc16_spanCodes_le_of_gens [256, 128, 68, 32, 20, 12, 2, 1]
    (actionW (codeMat 84) (codeMat 92) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 1 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 92) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step109wc16s1_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 116 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc16_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 92) (codeMat 2) = codeMat 128 := by
      unfold actionA
      rw [step109wc16s1_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 116 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc16_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 70 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 70 (by decide)
    have hact : actionA (codeMat 84) (codeMat 92) (codeMat 70) = codeMat 68 := by
      unfold actionA
      rw [step109wc16s1_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 70 * (codeMat 116 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc16_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 92) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc16s1_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 116 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc16_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 80 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 80 (by decide)
    have hact : actionA (codeMat 84) (codeMat 92) (codeMat 80) = codeMat 20 := by
      unfold actionA
      rw [step109wc16s1_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 80 * (codeMat 116 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc16_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 112 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 112 (by decide)
    have hact : actionA (codeMat 84) (codeMat 92) (codeMat 112) = codeMat 12 := by
      unfold actionA
      rw [step109wc16s1_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 112 * (codeMat 116 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc16_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 92) (codeMat 128) = codeMat 2 := by
      unfold actionA
      rw [step109wc16s1_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 116 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc16_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 92) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step109wc16s1_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 116 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc16_codeMat_mem_actionW_of_witness hw hact

theorem step109wc16s1Dispatch :
    QuotientRankAtLeast (o16SourceU_wc ⟨1, by omega⟩) 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 92 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 92) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 92) hP hQ flatW_3 9
      flatSeed_3
  exact quotientRankAtLeast_mono step109wc16s1_contain hAct


private theorem step109wc16s2_QtInv :
    (codeMat 212 : Mat3).transpose⁻¹ = (codeMat 86 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 212 : Mat3).transpose * (codeMat 86 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc16s2_contain :
    (o16SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 161) (codeMat 212) flatW_2 := by
  change spanCodes [256, 144, 80, 32, 8, 4, 2, 1] ≤ actionW (codeMat 161) (codeMat 212) flatW_2
  apply step109wc16_spanCodes_le_of_gens [256, 144, 80, 32, 8, 4, 2, 1]
    (actionW (codeMat 161) (codeMat 212) flatW_2)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 8 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 161) (codeMat 212) (codeMat 8) = codeMat 256 := by
      unfold actionA
      rw [step109wc16s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 8 * (codeMat 86 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc16_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 432 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 432 (by decide)
    have hact : actionA (codeMat 161) (codeMat 212) (codeMat 432) = codeMat 144 := by
      unfold actionA
      rw [step109wc16s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 432 * (codeMat 86 : Mat3).transpose = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc16_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 416 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 416 (by decide)
    have hact : actionA (codeMat 161) (codeMat 212) (codeMat 416) = codeMat 80 := by
      unfold actionA
      rw [step109wc16s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 416 * (codeMat 86 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc16_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 64 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 64 (by decide)
    have hact : actionA (codeMat 161) (codeMat 212) (codeMat 64) = codeMat 32 := by
      unfold actionA
      rw [step109wc16s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 64 * (codeMat 86 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc16_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 256 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 161) (codeMat 212) (codeMat 256) = codeMat 8 := by
      unfold actionA
      rw [step109wc16s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 256 * (codeMat 86 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc16_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 212) (codeMat 1) = codeMat 4 := by
      unfold actionA
      rw [step109wc16s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 86 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc16_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 6 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 6 (by decide)
    have hact : actionA (codeMat 161) (codeMat 212) (codeMat 6) = codeMat 2 := by
      unfold actionA
      rw [step109wc16s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 6 * (codeMat 86 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc16_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 4 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 4 (by decide)
    have hact : actionA (codeMat 161) (codeMat 212) (codeMat 4) = codeMat 1 := by
      unfold actionA
      rw [step109wc16s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 4 * (codeMat 86 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc16_codeMat_mem_actionW_of_witness hw hact

theorem step109wc16s2Dispatch :
    QuotientRankAtLeast (o16SourceU_wc ⟨2, by omega⟩) 6 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 212 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 212) flatW_2) 6 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 212) hP hQ flatW_2 6
      flatSeed_2
  exact quotientRankAtLeast_mono step109wc16s2_contain hAct

theorem step109wc16_all_dispatch (i : Fin 3) :
    QuotientRankAtLeast (o16SourceU_wc i) (o16SourceLb_wc i) := by
  fin_cases i
  · exact step109wc16s0Dispatch
  · exact step109wc16s1Dispatch
  · exact step109wc16s2Dispatch

theorem step109_orbit16_lb12_wc : QuotientRankAtLeast o16W_wc 12 :=
  o16Lb12_wc step109wc16_all_dispatch

end QiushiMatmul
