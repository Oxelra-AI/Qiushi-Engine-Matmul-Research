import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit25Consumer
import QiushiOrbit5FP
import QiushiFlattenSeeds

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc25_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc25_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc25s0_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc25s0_contain :
    (o25SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 273) (codeMat 140) orbit5W := by
  change spanCodes [256, 80, 32, 8, 4, 2, 1] ≤ actionW (codeMat 273) (codeMat 140) orbit5W
  apply step109wc25_spanCodes_le_of_gens [256, 80, 32, 8, 4, 2, 1]
    (actionW (codeMat 273) (codeMat 140) orbit5W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 64 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 64 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 64) = codeMat 256 := by
      unfold actionA
      rw [step109wc25s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 64 * (codeMat 98 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc25_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 160 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 160) = codeMat 80 := by
      unfold actionA
      rw [step109wc25s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 160 * (codeMat 98 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc25_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc25s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc25_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 16 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 16 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 16) = codeMat 8 := by
      unfold actionA
      rw [step109wc25s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 16 * (codeMat 98 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc25_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 1) = codeMat 4 := by
      unfold actionA
      rw [step109wc25s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc25_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 4 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 4 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 4) = codeMat 2 := by
      unfold actionA
      rw [step109wc25s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 4 * (codeMat 98 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc25_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc25s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc25_codeMat_mem_actionW_of_witness hw hact

theorem step109wc25s0Dispatch :
    QuotientRankAtLeast (o25SourceU_wc ⟨0, by omega⟩) 9 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 140) orbit5W) 9 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 140) hP hQ orbit5W 9
      orbit5_lb9
  exact quotientRankAtLeast_mono step109wc25s0_contain hAct


private theorem step109wc25s1_QtInv :
    (codeMat 401 : Mat3).transpose⁻¹ = (codeMat 401 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 401 : Mat3).transpose * (codeMat 401 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc25s1_contain :
    (o25SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 273) (codeMat 401) flatW_7 := by
  change spanCodes [256, 80, 48, 8, 4, 2, 1] ≤ actionW (codeMat 273) (codeMat 401) flatW_7
  apply step109wc25_spanCodes_le_of_gens [256, 80, 48, 8, 4, 2, 1]
    (actionW (codeMat 273) (codeMat 401) flatW_7)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 256 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 273) (codeMat 401) (codeMat 256) = codeMat 256 := by
      unfold actionA
      rw [step109wc25s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 256 * (codeMat 401 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc25_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 112 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 112 (by decide)
    have hact : actionA (codeMat 273) (codeMat 401) (codeMat 112) = codeMat 80 := by
      unfold actionA
      rw [step109wc25s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 112 * (codeMat 401 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc25_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 16 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 16 (by decide)
    have hact : actionA (codeMat 273) (codeMat 401) (codeMat 16) = codeMat 48 := by
      unfold actionA
      rw [step109wc25s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 16 * (codeMat 401 : Mat3).transpose = codeMat 48
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc25_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 401) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step109wc25s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 401 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc25_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 4 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 4 (by decide)
    have hact : actionA (codeMat 273) (codeMat 401) (codeMat 4) = codeMat 4 := by
      unfold actionA
      rw [step109wc25s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 4 * (codeMat 401 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc25_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 6 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 6 (by decide)
    have hact : actionA (codeMat 273) (codeMat 401) (codeMat 6) = codeMat 2 := by
      unfold actionA
      rw [step109wc25s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 6 * (codeMat 401 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc25_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 1 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 401) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc25s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 401 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc25_codeMat_mem_actionW_of_witness hw hact

theorem step109wc25s1Dispatch :
    QuotientRankAtLeast (o25SourceU_wc ⟨1, by omega⟩) 9 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 401) flatW_7) 9 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 401) hP hQ flatW_7 9
      flatSeed_7
  exact quotientRankAtLeast_mono step109wc25s1_contain hAct


private theorem step109wc25s2_QtInv :
    (codeMat 98 : Mat3).transpose⁻¹ = (codeMat 140 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 98 : Mat3).transpose * (codeMat 140 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc25s2_contain :
    (o25SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 161) (codeMat 98) flatW_7 := by
  change spanCodes [256, 128, 80, 8, 4, 2, 1] ≤ actionW (codeMat 161) (codeMat 98) flatW_7
  apply step109wc25_spanCodes_le_of_gens [256, 128, 80, 8, 4, 2, 1]
    (actionW (codeMat 161) (codeMat 98) flatW_7)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 16 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 16 (by decide)
    have hact : actionA (codeMat 161) (codeMat 98) (codeMat 16) = codeMat 256 := by
      unfold actionA
      rw [step109wc25s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 16 * (codeMat 140 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc25_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 8 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 161) (codeMat 98) (codeMat 8) = codeMat 128 := by
      unfold actionA
      rw [step109wc25s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 8 * (codeMat 140 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc25_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 96 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 96 (by decide)
    have hact : actionA (codeMat 161) (codeMat 98) (codeMat 96) = codeMat 80 := by
      unfold actionA
      rw [step109wc25s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 96 * (codeMat 140 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc25_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 161) (codeMat 98) (codeMat 256) = codeMat 8 := by
      unfold actionA
      rw [step109wc25s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 256 * (codeMat 140 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc25_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 98) (codeMat 2) = codeMat 4 := by
      unfold actionA
      rw [step109wc25s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 140 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc25_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 98) (codeMat 1) = codeMat 2 := by
      unfold actionA
      rw [step109wc25s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 140 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc25_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 4 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 4 (by decide)
    have hact : actionA (codeMat 161) (codeMat 98) (codeMat 4) = codeMat 1 := by
      unfold actionA
      rw [step109wc25s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 4 * (codeMat 140 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc25_codeMat_mem_actionW_of_witness hw hact

theorem step109wc25s2Dispatch :
    QuotientRankAtLeast (o25SourceU_wc ⟨2, by omega⟩) 9 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 98) flatW_7) 9 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 98) hP hQ flatW_7 9
      flatSeed_7
  exact quotientRankAtLeast_mono step109wc25s2_contain hAct


private theorem step109wc25s3_QtInv :
    (codeMat 226 : Mat3).transpose⁻¹ = (codeMat 141 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 226 : Mat3).transpose * (codeMat 141 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc25s3_contain :
    (o25SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 161) (codeMat 226) flatW_7 := by
  change spanCodes [256, 144, 80, 8, 4, 2, 1] ≤ actionW (codeMat 161) (codeMat 226) flatW_7
  apply step109wc25_spanCodes_le_of_gens [256, 144, 80, 8, 4, 2, 1]
    (actionW (codeMat 161) (codeMat 226) flatW_7)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 16 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 16 (by decide)
    have hact : actionA (codeMat 161) (codeMat 226) (codeMat 16) = codeMat 256 := by
      unfold actionA
      rw [step109wc25s3_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 16 * (codeMat 141 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc25_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 360 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 360 (by decide)
    have hact : actionA (codeMat 161) (codeMat 226) (codeMat 360) = codeMat 144 := by
      unfold actionA
      rw [step109wc25s3_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 360 * (codeMat 141 : Mat3).transpose = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc25_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 352 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 352 (by decide)
    have hact : actionA (codeMat 161) (codeMat 226) (codeMat 352) = codeMat 80 := by
      unfold actionA
      rw [step109wc25s3_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 352 * (codeMat 141 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc25_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 161) (codeMat 226) (codeMat 256) = codeMat 8 := by
      unfold actionA
      rw [step109wc25s3_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 256 * (codeMat 141 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc25_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 226) (codeMat 2) = codeMat 4 := by
      unfold actionA
      rw [step109wc25s3_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 141 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc25_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 5 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 5 (by decide)
    have hact : actionA (codeMat 161) (codeMat 226) (codeMat 5) = codeMat 2 := by
      unfold actionA
      rw [step109wc25s3_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 5 * (codeMat 141 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc25_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 4 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 4 (by decide)
    have hact : actionA (codeMat 161) (codeMat 226) (codeMat 4) = codeMat 1 := by
      unfold actionA
      rw [step109wc25s3_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 4 * (codeMat 141 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc25_codeMat_mem_actionW_of_witness hw hact

theorem step109wc25s3Dispatch :
    QuotientRankAtLeast (o25SourceU_wc ⟨3, by omega⟩) 9 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 226 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 226) flatW_7) 9 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 226) hP hQ flatW_7 9
      flatSeed_7
  exact quotientRankAtLeast_mono step109wc25s3_contain hAct


private theorem step109wc25s4_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc25s4_contain :
    (o25SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 161) (codeMat 161) flatW_2 := by
  change spanCodes [256, 160, 64, 16, 8, 4, 2, 1] ≤ actionW (codeMat 161) (codeMat 161) flatW_2
  apply step109wc25_spanCodes_le_of_gens [256, 160, 64, 16, 8, 4, 2, 1]
    (actionW (codeMat 161) (codeMat 161) flatW_2)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 16 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 16 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 16) = codeMat 256 := by
      unfold actionA
      rw [step109wc25s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 16 * (codeMat 161 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc25_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 160) = codeMat 160 := by
      unfold actionA
      rw [step109wc25s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * (codeMat 161 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc25_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 8) = codeMat 64 := by
      unfold actionA
      rw [step109wc25s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 8 * (codeMat 161 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc25_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 256) = codeMat 16 := by
      unfold actionA
      rw [step109wc25s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 256 * (codeMat 161 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc25_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 64 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 64 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 64) = codeMat 8 := by
      unfold actionA
      rw [step109wc25s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 64 * (codeMat 161 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc25_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 2) = codeMat 4 := by
      unfold actionA
      rw [step109wc25s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 161 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc25_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 4 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 4 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 4) = codeMat 2 := by
      unfold actionA
      rw [step109wc25s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 4 * (codeMat 161 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc25_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 1 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc25s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc25_codeMat_mem_actionW_of_witness hw hact

theorem step109wc25s4Dispatch :
    QuotientRankAtLeast (o25SourceU_wc ⟨4, by omega⟩) 6 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 161) flatW_2) 6 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 161) hP hQ flatW_2 6
      flatSeed_2
  exact quotientRankAtLeast_mono step109wc25s4_contain hAct

theorem step109wc25_all_dispatch (i : Fin 5) :
    QuotientRankAtLeast (o25SourceU_wc i) (o25SourceLb_wc i) := by
  fin_cases i
  · exact step109wc25s0Dispatch
  · exact step109wc25s1Dispatch
  · exact step109wc25s2Dispatch
  · exact step109wc25s3Dispatch
  · exact step109wc25s4Dispatch

theorem step109_orbit25_lb11_wc : QuotientRankAtLeast o25W_wc 11 :=
  o25Lb11_wc step109wc25_all_dispatch

end QiushiMatmul
