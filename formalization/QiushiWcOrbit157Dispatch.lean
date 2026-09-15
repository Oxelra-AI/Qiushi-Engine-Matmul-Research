import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit157Consumer
import QiushiMonoOrbit71From17
import QiushiStep99Mono3032
import QiushiOrbit14FP

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc157_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc157_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc157s0_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc157s0_contain :
    (o157SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 273) (codeMat 273) o71W_mono := by
  change spanCodes [128, 68, 32, 20, 10, 1] ≤ actionW (codeMat 273) (codeMat 273) o71W_mono
  apply step109wc157_spanCodes_le_of_gens [128, 68, 32, 20, 10, 1]
    (actionW (codeMat 273) (codeMat 273) o71W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 128 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 128) = codeMat 128 := by
      unfold actionA
      rw [step109wc157s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 128 * (codeMat 273 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 68 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 68) = codeMat 68 := by
      unfold actionA
      rw [step109wc157s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 68 * (codeMat 273 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 32 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 32) = codeMat 32 := by
      unfold actionA
      rw [step109wc157s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 32 * (codeMat 273 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 20 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 20 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 20) = codeMat 20 := by
      unfold actionA
      rw [step109wc157s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 20 * (codeMat 273 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 10 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step109wc157s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 10 * (codeMat 273 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc157s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact

theorem step109wc157s0Dispatch :
    QuotientRankAtLeast (o157SourceU_wc ⟨0, by omega⟩) 14 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 273) o71W_mono) 14 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 273) hP hQ o71W_mono 14
      orbit71_lb14_mono
  exact quotientRankAtLeast_mono step109wc157s0_contain hAct


private theorem step109wc157s1_QtInv :
    (codeMat 93 : Mat3).transpose⁻¹ = (codeMat 372 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 93 : Mat3).transpose * (codeMat 372 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc157s1_contain :
    (o157SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 282) (codeMat 93) o71W_mono := by
  change spanCodes [262, 128, 32, 20, 10, 1] ≤ actionW (codeMat 282) (codeMat 93) o71W_mono
  apply step109wc157_spanCodes_le_of_gens [262, 128, 32, 20, 10, 1]
    (actionW (codeMat 282) (codeMat 93) o71W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 91 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 91 (by decide)
    have hact : actionA (codeMat 282) (codeMat 93) (codeMat 91) = codeMat 262 := by
      unfold actionA
      rw [step109wc157s1_QtInv]
      show (codeMat 282 : Mat3).transpose * codeMat 91 * (codeMat 372 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 128 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 282) (codeMat 93) (codeMat 128) = codeMat 128 := by
      unfold actionA
      rw [step109wc157s1_QtInv]
      show (codeMat 282 : Mat3).transpose * codeMat 128 * (codeMat 372 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 282) (codeMat 93) (codeMat 1) = codeMat 32 := by
      unfold actionA
      rw [step109wc157s1_QtInv]
      show (codeMat 282 : Mat3).transpose * codeMat 1 * (codeMat 372 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 11 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 282) (codeMat 93) (codeMat 11) = codeMat 20 := by
      unfold actionA
      rw [step109wc157s1_QtInv]
      show (codeMat 282 : Mat3).transpose * codeMat 11 * (codeMat 372 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 21 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 21 (by decide)
    have hact : actionA (codeMat 282) (codeMat 93) (codeMat 21) = codeMat 10 := by
      unfold actionA
      rw [step109wc157s1_QtInv]
      show (codeMat 282 : Mat3).transpose * codeMat 21 * (codeMat 372 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 63 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 63 (by decide)
    have hact : actionA (codeMat 282) (codeMat 93) (codeMat 63) = codeMat 1 := by
      unfold actionA
      rw [step109wc157s1_QtInv]
      show (codeMat 282 : Mat3).transpose * codeMat 63 * (codeMat 372 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact

theorem step109wc157s1Dispatch :
    QuotientRankAtLeast (o157SourceU_wc ⟨1, by omega⟩) 14 := by
  have hP : Invertible (codeMat 282 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 93 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 282) (codeMat 93) o71W_mono) 14 :=
    @quotientRankAtLeast_action (codeMat 282) (codeMat 93) hP hQ o71W_mono 14
      orbit71_lb14_mono
  exact quotientRankAtLeast_mono step109wc157s1_contain hAct


private theorem step109wc157s2_QtInv :
    (codeMat 372 : Mat3).transpose⁻¹ = (codeMat 93 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 372 : Mat3).transpose * (codeMat 93 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc157s2_contain :
    (o157SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 267) (codeMat 372) o71W_mono := by
  change spanCodes [322, 128, 32, 20, 10, 1] ≤ actionW (codeMat 267) (codeMat 372) o71W_mono
  apply step109wc157_spanCodes_le_of_gens [322, 128, 32, 20, 10, 1]
    (actionW (codeMat 267) (codeMat 372) o71W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 208 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 208 (by decide)
    have hact : actionA (codeMat 267) (codeMat 372) (codeMat 208) = codeMat 322 := by
      unfold actionA
      rw [step109wc157s2_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 208 * (codeMat 93 : Mat3).transpose = codeMat 322
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 128 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 267) (codeMat 372) (codeMat 128) = codeMat 128 := by
      unfold actionA
      rw [step109wc157s2_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 128 * (codeMat 93 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 63 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 63 (by decide)
    have hact : actionA (codeMat 267) (codeMat 372) (codeMat 63) = codeMat 32 := by
      unfold actionA
      rw [step109wc157s2_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 63 * (codeMat 93 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 42 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 42 (by decide)
    have hact : actionA (codeMat 267) (codeMat 372) (codeMat 42) = codeMat 20 := by
      unfold actionA
      rw [step109wc157s2_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 42 * (codeMat 93 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 52 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 52 (by decide)
    have hact : actionA (codeMat 267) (codeMat 372) (codeMat 52) = codeMat 10 := by
      unfold actionA
      rw [step109wc157s2_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 52 * (codeMat 93 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 267) (codeMat 372) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step109wc157s2_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 32 * (codeMat 93 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact

theorem step109wc157s2Dispatch :
    QuotientRankAtLeast (o157SourceU_wc ⟨2, by omega⟩) 14 := by
  have hP : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 372 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 267) (codeMat 372) o71W_mono) 14 :=
    @quotientRankAtLeast_action (codeMat 267) (codeMat 372) hP hQ o71W_mono 14
      orbit71_lb14_mono
  exact quotientRankAtLeast_mono step109wc157s2_contain hAct


private theorem step109wc157s3_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc157s3_contain :
    (o157SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 273) (codeMat 273) monoW_32 := by
  change spanCodes [128, 32, 20, 8, 2, 1] ≤ actionW (codeMat 273) (codeMat 273) monoW_32
  apply step109wc157_spanCodes_le_of_gens [128, 32, 20, 8, 2, 1]
    (actionW (codeMat 273) (codeMat 273) monoW_32)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 128 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 128) = codeMat 128 := by
      unfold actionA
      rw [step109wc157s3_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 128 * (codeMat 273 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 32 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 32) = codeMat 32 := by
      unfold actionA
      rw [step109wc157s3_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 32 * (codeMat 273 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 20 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 20 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 20) = codeMat 20 := by
      unfold actionA
      rw [step109wc157s3_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 20 * (codeMat 273 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step109wc157s3_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 273 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc157s3_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc157s3_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact

theorem step109wc157s3Dispatch :
    QuotientRankAtLeast (o157SourceU_wc ⟨3, by omega⟩) 12 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 273) monoW_32) 12 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 273) hP hQ monoW_32 12
      step99_mono_32_lb12
  exact quotientRankAtLeast_mono step109wc157s3_contain hAct


private theorem step109wc157s4_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc157s4_contain :
    (o157SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 266) (codeMat 84) monoW_32 := by
  change spanCodes [128, 32, 16, 10, 4, 1] ≤ actionW (codeMat 266) (codeMat 84) monoW_32
  apply step109wc157_spanCodes_le_of_gens [128, 32, 16, 10, 4, 1]
    (actionW (codeMat 266) (codeMat 84) monoW_32)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 128 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 266) (codeMat 84) (codeMat 128) = codeMat 128 := by
      unfold actionA
      rw [step109wc157s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 128 * (codeMat 84 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 84) (codeMat 1) = codeMat 32 := by
      unfold actionA
      rw [step109wc157s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 84 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 84) (codeMat 2) = codeMat 16 := by
      unfold actionA
      rw [step109wc157s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 84 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 20 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 20 (by decide)
    have hact : actionA (codeMat 266) (codeMat 84) (codeMat 20) = codeMat 10 := by
      unfold actionA
      rw [step109wc157s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 20 * (codeMat 84 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 84) (codeMat 8) = codeMat 4 := by
      unfold actionA
      rw [step109wc157s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 84 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 266) (codeMat 84) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step109wc157s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 84 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact

theorem step109wc157s4Dispatch :
    QuotientRankAtLeast (o157SourceU_wc ⟨4, by omega⟩) 12 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 84) monoW_32) 12 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 84) hP hQ monoW_32 12
      step99_mono_32_lb12
  exact quotientRankAtLeast_mono step109wc157s4_contain hAct


private theorem step109wc157s5_QtInv :
    (codeMat 369 : Mat3).transpose⁻¹ = (codeMat 377 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 369 : Mat3).transpose * (codeMat 377 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc157s5_contain :
    (o157SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 267) (codeMat 369) monoW_32 := by
  change spanCodes [128, 32, 18, 10, 6, 1] ≤ actionW (codeMat 267) (codeMat 369) monoW_32
  apply step109wc157_spanCodes_le_of_gens [128, 32, 18, 10, 6, 1]
    (actionW (codeMat 267) (codeMat 369) monoW_32)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 128 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 267) (codeMat 369) (codeMat 128) = codeMat 128 := by
      unfold actionA
      rw [step109wc157s5_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 128 * (codeMat 377 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 54 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 54 (by decide)
    have hact : actionA (codeMat 267) (codeMat 369) (codeMat 54) = codeMat 32 := by
      unfold actionA
      rw [step109wc157s5_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 54 * (codeMat 377 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 267) (codeMat 369) (codeMat 2) = codeMat 18 := by
      unfold actionA
      rw [step109wc157s5_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 2 * (codeMat 377 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 61 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 61 (by decide)
    have hact : actionA (codeMat 267) (codeMat 369) (codeMat 61) = codeMat 10 := by
      unfold actionA
      rw [step109wc157s5_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 61 * (codeMat 377 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 32 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 267) (codeMat 369) (codeMat 32) = codeMat 6 := by
      unfold actionA
      rw [step109wc157s5_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 32 * (codeMat 377 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 40 ∈ monoW_32 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 267) (codeMat 369) (codeMat 40) = codeMat 1 := by
      unfold actionA
      rw [step109wc157s5_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 40 * (codeMat 377 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact

theorem step109wc157s5Dispatch :
    QuotientRankAtLeast (o157SourceU_wc ⟨5, by omega⟩) 12 := by
  have hP : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 369 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 267) (codeMat 369) monoW_32) 12 :=
    @quotientRankAtLeast_action (codeMat 267) (codeMat 369) hP hQ monoW_32 12
      step99_mono_32_lb12
  exact quotientRankAtLeast_mono step109wc157s5_contain hAct


private theorem step109wc157s6_QtInv :
    (codeMat 421 : Mat3).transpose⁻¹ = (codeMat 179 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 421 : Mat3).transpose * (codeMat 179 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc157s6_contain :
    (o157SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 271) (codeMat 421) orbit14W := by
  change spanCodes [258, 128, 66, 32, 20, 10, 1] ≤ actionW (codeMat 271) (codeMat 421) orbit14W
  apply step109wc157_spanCodes_le_of_gens [258, 128, 66, 32, 20, 10, 1]
    (actionW (codeMat 271) (codeMat 421) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 480 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 480 (by decide)
    have hact : actionA (codeMat 271) (codeMat 421) (codeMat 480) = codeMat 258 := by
      unfold actionA
      rw [step109wc157s6_QtInv]
      show (codeMat 271 : Mat3).transpose * codeMat 480 * (codeMat 179 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 271) (codeMat 421) (codeMat 256) = codeMat 128 := by
      unfold actionA
      rw [step109wc157s6_QtInv]
      show (codeMat 271 : Mat3).transpose * codeMat 256 * (codeMat 179 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 271) (codeMat 421) (codeMat 96) = codeMat 66 := by
      unfold actionA
      rw [step109wc157s6_QtInv]
      show (codeMat 271 : Mat3).transpose * codeMat 96 * (codeMat 179 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 511 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 511 (by decide)
    have hact : actionA (codeMat 271) (codeMat 421) (codeMat 511) = codeMat 32 := by
      unfold actionA
      rw [step109wc157s6_QtInv]
      show (codeMat 271 : Mat3).transpose * codeMat 511 * (codeMat 179 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 284 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 284 (by decide)
    have hact : actionA (codeMat 271) (codeMat 421) (codeMat 284) = codeMat 20 := by
      unfold actionA
      rw [step109wc157s6_QtInv]
      show (codeMat 271 : Mat3).transpose * codeMat 284 * (codeMat 179 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 105 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 105 (by decide)
    have hact : actionA (codeMat 271) (codeMat 421) (codeMat 105) = codeMat 10 := by
      unfold actionA
      rw [step109wc157s6_QtInv]
      show (codeMat 271 : Mat3).transpose * codeMat 105 * (codeMat 179 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 271) (codeMat 421) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc157s6_QtInv]
      show (codeMat 271 : Mat3).transpose * codeMat 8 * (codeMat 179 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact

theorem step109wc157s6Dispatch :
    QuotientRankAtLeast (o157SourceU_wc ⟨6, by omega⟩) 12 := by
  have hP : Invertible (codeMat 271 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 421 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 271) (codeMat 421) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 271) (codeMat 421) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc157s6_contain hAct


private theorem step109wc157s7_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc157s7_contain :
    (o157SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 277) (codeMat 140) orbit14W := by
  change spanCodes [260, 128, 64, 32, 20, 10, 1] ≤ actionW (codeMat 277) (codeMat 140) orbit14W
  apply step109wc157_spanCodes_le_of_gens [260, 128, 64, 32, 20, 10, 1]
    (actionW (codeMat 277) (codeMat 140) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 277) (codeMat 140) (codeMat 1) = codeMat 260 := by
      unfold actionA
      rw [step109wc157s7_QtInv]
      show (codeMat 277 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 277) (codeMat 140) (codeMat 256) = codeMat 128 := by
      unfold actionA
      rw [step109wc157s7_QtInv]
      show (codeMat 277 : Mat3).transpose * codeMat 256 * (codeMat 98 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 277) (codeMat 140) (codeMat 128) = codeMat 64 := by
      unfold actionA
      rw [step109wc157s7_QtInv]
      show (codeMat 277 : Mat3).transpose * codeMat 128 * (codeMat 98 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 277) (codeMat 140) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc157s7_QtInv]
      show (codeMat 277 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 97 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 97 (by decide)
    have hact : actionA (codeMat 277) (codeMat 140) (codeMat 97) = codeMat 20 := by
      unfold actionA
      rw [step109wc157s7_QtInv]
      show (codeMat 277 : Mat3).transpose * codeMat 97 * (codeMat 98 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 276 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 276 (by decide)
    have hact : actionA (codeMat 277) (codeMat 140) (codeMat 276) = codeMat 10 := by
      unfold actionA
      rw [step109wc157s7_QtInv]
      show (codeMat 277 : Mat3).transpose * codeMat 276 * (codeMat 98 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 130 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 130 (by decide)
    have hact : actionA (codeMat 277) (codeMat 140) (codeMat 130) = codeMat 1 := by
      unfold actionA
      rw [step109wc157s7_QtInv]
      show (codeMat 277 : Mat3).transpose * codeMat 130 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact

theorem step109wc157s7Dispatch :
    QuotientRankAtLeast (o157SourceU_wc ⟨7, by omega⟩) 12 := by
  have hP : Invertible (codeMat 277 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 277) (codeMat 140) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 277) (codeMat 140) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc157s7_contain hAct


private theorem step109wc157s8_QtInv :
    (codeMat 233 : Mat3).transpose⁻¹ = (codeMat 233 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 233 : Mat3).transpose * (codeMat 233 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc157s8_contain :
    (o157SourceU_wc ⟨8, by omega⟩) ≤ actionW (codeMat 286) (codeMat 233) orbit14W := by
  change spanCodes [256, 128, 70, 32, 20, 10, 1] ≤ actionW (codeMat 286) (codeMat 233) orbit14W
  apply step109wc157_spanCodes_le_of_gens [256, 128, 70, 32, 20, 10, 1]
    (actionW (codeMat 286) (codeMat 233) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 286) (codeMat 233) (codeMat 128) = codeMat 256 := by
      unfold actionA
      rw [step109wc157s8_QtInv]
      show (codeMat 286 : Mat3).transpose * codeMat 128 * (codeMat 233 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 286) (codeMat 233) (codeMat 256) = codeMat 128 := by
      unfold actionA
      rw [step109wc157s8_QtInv]
      show (codeMat 286 : Mat3).transpose * codeMat 256 * (codeMat 233 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 118 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 118 (by decide)
    have hact : actionA (codeMat 286) (codeMat 233) (codeMat 118) = codeMat 70 := by
      unfold actionA
      rw [step109wc157s8_QtInv]
      show (codeMat 286 : Mat3).transpose * codeMat 118 * (codeMat 233 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 130 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 130 (by decide)
    have hact : actionA (codeMat 286) (codeMat 233) (codeMat 130) = codeMat 32 := by
      unfold actionA
      rw [step109wc157s8_QtInv]
      show (codeMat 286 : Mat3).transpose * codeMat 130 * (codeMat 233 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 406 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 406 (by decide)
    have hact : actionA (codeMat 286) (codeMat 233) (codeMat 406) = codeMat 20 := by
      unfold actionA
      rw [step109wc157s8_QtInv]
      show (codeMat 286 : Mat3).transpose * codeMat 406 * (codeMat 233 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 227 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 227 (by decide)
    have hact : actionA (codeMat 286) (codeMat 233) (codeMat 227) = codeMat 10 := by
      unfold actionA
      rw [step109wc157s8_QtInv]
      show (codeMat 286 : Mat3).transpose * codeMat 227 * (codeMat 233 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 511 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 511 (by decide)
    have hact : actionA (codeMat 286) (codeMat 233) (codeMat 511) = codeMat 1 := by
      unfold actionA
      rw [step109wc157s8_QtInv]
      show (codeMat 286 : Mat3).transpose * codeMat 511 * (codeMat 233 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc157_codeMat_mem_actionW_of_witness hw hact

theorem step109wc157s8Dispatch :
    QuotientRankAtLeast (o157SourceU_wc ⟨8, by omega⟩) 12 := by
  have hP : Invertible (codeMat 286 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 233 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 286) (codeMat 233) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 286) (codeMat 233) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc157s8_contain hAct

theorem step109wc157_all_dispatch (i : Fin 9) :
    QuotientRankAtLeast (o157SourceU_wc i) (o157SourceLb_wc i) := by
  fin_cases i
  · exact step109wc157s0Dispatch
  · exact step109wc157s1Dispatch
  · exact step109wc157s2Dispatch
  · exact step109wc157s3Dispatch
  · exact step109wc157s4Dispatch
  · exact step109wc157s5Dispatch
  · exact step109wc157s6Dispatch
  · exact step109wc157s7Dispatch
  · exact step109wc157s8Dispatch

theorem step109_orbit157_lb15_wc : QuotientRankAtLeast o157W_wc 15 :=
  o157Lb15_wc step109wc157_all_dispatch

end QiushiMatmul
