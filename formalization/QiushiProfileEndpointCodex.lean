import QiushiProfileForcingStep47
import QiushiSplitRankBound
import QiushiNoDecompBelow20
import QiushiDropTerm
import QiushiRankBridge

/-!
The arithmetic/minimality endpoint of the root profile obligation.  This
module deliberately exposes the two still-geometric inputs—high-factor and
rank-three caps—as hypotheses, and discharges everything after those caps.
-/

open Matrix BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

set_option maxRecDepth 200000

def codexDropTermA {r : Nat} (D : TensorEntryDecomp (r + 1))
    (t₀ : Fin (r + 1)) (hA : D.A t₀ = 0) : TensorEntryDecomp r where
  A := fun i => D.A (t₀.succAbove i)
  B := fun i => D.B (t₀.succAbove i)
  C := fun i => D.C (t₀.succAbove i)
  entry_identity := by
    intro a b c
    have orig := D.entry_identity a b c
    rw [orig, Fin.sum_univ_succAbove _ t₀]
    simp only [hA, Matrix.zero_apply, zero_mul, zero_add]

theorem codex_nonzero_A_of_noDecompBelow {r : Nat} (D : TensorEntryDecomp r)
    (hshort : ∀ m : Nat, m < r → TensorEntryDecomp m → False)
    (t : Fin r) : D.A t ≠ 0 := by
  intro hA
  cases r with
  | zero => exact Fin.elim0 t
  | succ n =>
      exact hshort n (Nat.lt_succ_of_le le_rfl) (codexDropTermA D t hA)

lemma codex_matrix_rank_le_three (M : Mat3) : M.rank ≤ 3 := by
  simpa using M.rank_le_card_width

set_option maxHeartbeats 24000000 in
private theorem codex_nonzero_code_rank_positive : ∀ c : Fin 512,
    c.val ≠ 0 → 1 ≤ rankCode c.val := by
  decide +revert

lemma codex_matrix_rank_positive (M : Mat3) (hM : M ≠ 0) : 1 ≤ M.rank := by
  let c := matrixCode M
  have hc : c.val ≠ 0 := by
    intro hc0
    apply hM
    have hdecode : codeMat c.val = M := by
      simpa [c, matrixCode] using codeMat_matrixCode M
    rw [hc0] at hdecode
    have hz : (codeMat 0 : Mat3) = 0 := by decide
    simpa [hz] using hdecode.symm
  rw [rank_eq_rankCode M]
  simpa [c, matrixCode] using codex_nonzero_code_rank_positive c hc

set_option maxHeartbeats 24000000 in
private theorem codex_code_rank_three_det : ∀ c : Fin 512,
    rankCode c.val = 3 → (codeMat c.val : Mat3).det ≠ 0 := by
  decide +revert

lemma codex_det_ne_zero_of_rank_three (M : Mat3) (hM : M.rank = 3) :
    M.det ≠ 0 := by
  let c := matrixCode M
  have hdecode : codeMat c.val = M := by
    simpa [c, matrixCode] using codeMat_matrixCode M
  have hcRank : rankCode c.val = 3 := by
    rw [← rank_eq_rankCode_code c, hdecode]
    exact hM
  simpa [hdecode] using codex_code_rank_three_det c hcRank

/-- Once geometry supplies `highCount ≤ 4` and `rankThreeCount ≤ 3`, the exact
root-profile conclusion follows.  Thus these two caps are the complete
remaining interface after normalization/occupation. -/
theorem profile_endpoint_of_caps_codex
    (P : FinitePremises) (D : TensorEntryDecomp 20)
    (hhigh : highCount (fun t => (D.A t).rank) ≤ 4)
    (hthree : rankThreeCount (fun t => (D.A t).rank) ≤ 3) :
    ∃ t s : Fin 20,
      t ≠ s ∧ (D.A t).det ≠ 0 ∧ (D.A s).det ≠ 0 ∧
      (∑ u : Fin 20, (D.A u).rank) = Fintype.card SIdx ∧
      (∀ u : Fin 20, D.B u ≠ 0) ∧ (∀ u : Fin 20, D.C u ≠ 0) := by
  classical
  have hshort : ∀ m : Nat, m < 20 → TensorEntryDecomp m → False :=
    fun m hm E => no_decomp_below_20_from_finitePremises P m hm E
  have hA0 : ∀ t : Fin 20, D.A t ≠ 0 :=
    codex_nonzero_A_of_noDecompBelow D hshort
  have hBC := nonzero_BC_of_noDecompBelow D hshort
  have hprofile := forced_profile_from_rank_sum_and_high_cap
    (rk := fun t : Fin 20 => (D.A t).rank)
    (by decide)
    (fun t => codex_matrix_rank_positive (D.A t) (hA0 t))
    (fun t => codex_matrix_rank_le_three (D.A t))
    (split_rank_bound_from_entrywise D) hhigh hthree
  let T : Finset (Fin 20) := Finset.univ.filter fun t => (D.A t).rank = 3
  have hTcard : T.card = 3 := by
    simpa [T, rankThreeCount] using hprofile.2.1
  rcases Finset.card_eq_three.mp hTcard with
    ⟨t, s, z, hts, _htz, _hsz, hT⟩
  have htT : t ∈ T := by rw [hT]; simp
  have hsT : s ∈ T := by rw [hT]; simp
  have htRank : (D.A t).rank = 3 := (Finset.mem_filter.mp htT).2
  have hsRank : (D.A s).rank = 3 := (Finset.mem_filter.mp hsT).2
  refine ⟨t, s, hts,
    codex_det_ne_zero_of_rank_three (D.A t) htRank,
    codex_det_ne_zero_of_rank_three (D.A s) hsRank, ?_, ?_, ?_⟩
  · have hsum := hprofile.2.2.2
    have hcard : Fintype.card SIdx = 27 := by decide
    omega
  · exact fun u => (hBC u).1
  · exact fun u => (hBC u).2

end QiushiMatmul
end
