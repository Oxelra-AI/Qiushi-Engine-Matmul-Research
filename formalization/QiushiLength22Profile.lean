import QiushiBridge
import QiushiProfileForcingStep47
import QiushiRankBridge
import QiushiSaturationShared
import QiushiSplitRankBound

/-!
# Zero-A-excess restrictions at length 22

The saturation endpoint requires nonzero B- and C-factors.  At length 22 these
cannot currently be obtained from the conditional lower-bound interfaces, so
they are stated explicitly, together with nonzero A-factors needed for the
three-valued rank count.  No new mathematical premise record is introduced.
-/

open Matrix BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section

namespace QiushiMatmul

set_option maxRecDepth 200000

def rankOneCount {ι : Type*} [Fintype ι] (rk : ι → Nat) : Nat :=
  ∑ i : ι, if rk i = 1 then 1 else 0

private theorem tail_nonzero_code_rank_positive : ∀ c : Fin 512,
    c.val ≠ 0 → 1 ≤ rankCode c.val := by
  decide +revert

lemma tail_matrix_rank_positive (M : Mat3) (hM : M ≠ 0) : 1 ≤ M.rank := by
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
  simpa [c, matrixCode] using tail_nonzero_code_rank_positive c hc

lemma tail_matrix_rank_le_three (M : Mat3) : M.rank ≤ 3 := by
  simpa using M.rank_le_card_width

private theorem tail_code_rank_three_det : ∀ c : Fin 512,
    rankCode c.val = 3 → (codeMat c.val : Mat3).det ≠ 0 := by
  decide +revert

lemma tail_det_ne_zero_of_rank_three (M : Mat3) (hM : M.rank = 3) :
    M.det ≠ 0 := by
  let c := matrixCode M
  have hdecode : codeMat c.val = M := by
    simpa [c, matrixCode] using codeMat_matrixCode M
  have hcRank : rankCode c.val = 3 := by
    rw [← rank_eq_rankCode_code c, hdecode]
    exact hM
  simpa [hdecode] using tail_code_rank_three_det c hcRank

lemma rank_count_partition {ι : Type*} [Fintype ι] (rk : ι → Nat)
    (hpos : ∀ i, 1 ≤ rk i) (hupper : ∀ i, rk i ≤ 3) :
    rankOneCount rk + rankTwoCount rk + rankThreeCount rk = Fintype.card ι := by
  classical
  have hpoint : ∀ i : ι, rk i = 1 ∨ rk i = 2 ∨ rk i = 3 := by
    intro i
    have hp := hpos i
    have hu := hupper i
    omega
  have hterm : ∀ i : ι,
      (if rk i = 1 then 1 else 0) +
        (if rk i = 2 then 1 else 0) +
          (if rk i = 3 then 1 else 0) = 1 := by
    intro i
    rcases hpoint i with h1 | h23
    · simp [h1]
    · rcases h23 with h2 | h3
      · simp [h2]
      · simp [h3]
  calc
    rankOneCount rk + rankTwoCount rk + rankThreeCount rk =
        ∑ i : ι, ((if rk i = 1 then 1 else 0) +
          (if rk i = 2 then 1 else 0) +
            (if rk i = 3 then 1 else 0)) := by
      simp [rankOneCount, rankTwoCount, rankThreeCount,
        Finset.sum_add_distrib]
    _ = ∑ _i : ι, 1 := by
      apply Finset.sum_congr rfl
      intro i _
      exact hterm i
    _ = Fintype.card ι := by simp

theorem length22_A_rank_sum_ge_27 (D : TensorEntryDecomp 22) :
    27 ≤ ∑ t : Fin 22, (D.A t).rank :=
  split_rank_bound_from_entrywise D

/-- At zero A-split excess, two distinct invertible A-factors contradict the
unchanged saturation endpoint. -/
theorem length22_zero_A_excess_at_most_one_invertible
    (D : TensorEntryDecomp 22)
    (hrank : (∑ t : Fin 22, (D.A t).rank) = Fintype.card SIdx)
    (hB : ∀ t : Fin 22, D.B t ≠ 0)
    (hC : ∀ t : Fin 22, D.C t ≠ 0) :
    ∀ t s : Fin 22, (D.A t).det ≠ 0 → (D.A s).det ≠ 0 → t = s := by
  intro t s hAt hAs
  by_contra hts
  exact two_invertible_terms_contradict_from_A_rank_decomposition
    D.A D.B D.C (entrywise_to_split_sum D) hrank hB hC t s hts hAt hAs

theorem length22_zero_A_excess_rankThreeCount_le_one
    (D : TensorEntryDecomp 22)
    (hrank : (∑ t : Fin 22, (D.A t).rank) = Fintype.card SIdx)
    (hB : ∀ t : Fin 22, D.B t ≠ 0)
    (hC : ∀ t : Fin 22, D.C t ≠ 0) :
    rankThreeCount (fun t : Fin 22 => (D.A t).rank) ≤ 1 := by
  classical
  let T : Finset (Fin 22) := Finset.univ.filter fun t => (D.A t).rank = 3
  have hTcard : T.card = rankThreeCount (fun t : Fin 22 => (D.A t).rank) := by
    simp [T, rankThreeCount]
  rw [← hTcard]
  apply Finset.card_le_one.mpr
  intro t ht s hs
  apply length22_zero_A_excess_at_most_one_invertible D hrank hB hC
  · exact tail_det_ne_zero_of_rank_three _ (Finset.mem_filter.mp ht).2
  · exact tail_det_ne_zero_of_rank_three _ (Finset.mem_filter.mp hs).2

/-- The only zero-A-excess profiles compatible with saturation are
`(rank-one, rank-two, rank-three) = (17,5,0)` and `(18,3,1)`. -/
theorem length22_zero_A_excess_profiles
    (D : TensorEntryDecomp 22)
    (hA : ∀ t : Fin 22, D.A t ≠ 0)
    (hB : ∀ t : Fin 22, D.B t ≠ 0)
    (hC : ∀ t : Fin 22, D.C t ≠ 0)
    (hrank : (∑ t : Fin 22, (D.A t).rank) = Fintype.card SIdx) :
    (rankOneCount (fun t : Fin 22 => (D.A t).rank) = 17 ∧
      rankTwoCount (fun t : Fin 22 => (D.A t).rank) = 5 ∧
      rankThreeCount (fun t : Fin 22 => (D.A t).rank) = 0) ∨
    (rankOneCount (fun t : Fin 22 => (D.A t).rank) = 18 ∧
      rankTwoCount (fun t : Fin 22 => (D.A t).rank) = 3 ∧
      rankThreeCount (fun t : Fin 22 => (D.A t).rank) = 1) := by
  let rk : Fin 22 → Nat := fun t => (D.A t).rank
  have hpos : ∀ t, 1 ≤ rk t := fun t => tail_matrix_rank_positive _ (hA t)
  have hupper : ∀ t, rk t ≤ 3 := fun t => tail_matrix_rank_le_three _
  have hsum := rank_sum_eq_card_plus_high_plus_rankThree rk hpos hupper
  have hhigh := highCount_eq_rankTwo_add_rankThree rk hpos hupper
  have hpartition := rank_count_partition rk hpos hupper
  have hthree := length22_zero_A_excess_rankThreeCount_le_one D hrank hB hC
  have hcard22 : Fintype.card (Fin 22) = 22 := by decide
  have hcardS : Fintype.card SIdx = 27 := by decide
  change (∑ t : Fin 22, rk t) = Fintype.card SIdx at hrank
  change rankThreeCount rk ≤ 1 at hthree
  change
    (rankOneCount rk = 17 ∧ rankTwoCount rk = 5 ∧ rankThreeCount rk = 0) ∨
    (rankOneCount rk = 18 ∧ rankTwoCount rk = 3 ∧ rankThreeCount rk = 1)
  rcases Nat.eq_zero_or_pos (rankThreeCount rk) with hz | hp
  · left
    omega
  · right
    omega

end QiushiMatmul
end
