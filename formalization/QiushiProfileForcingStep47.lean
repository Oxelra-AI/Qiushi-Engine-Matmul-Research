import QiushiDefs

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-!
Profile-forcing finite spine.

This module starts the Lean profile-forcing thread needed for the final
`R_F2(T_<3,3,3>) >= 21` formalization.  It contains two checked pieces:

* an explicit 256-mask verification of the normalized AG(3,2) affine-plane cap;
* the arithmetic endpoint: for 20 nonzero A-factors with matrix ranks in
  `{1,2,3}`, total A-rank at least 27, at most four high-rank factors, and at
  most three rank-three factors, the high-rank profile is forced to be one
  rank-two and three rank-three factors and the total rank is exactly 27.
-/

open BigOperators

namespace QiushiMatmul

abbrev AG32Point := Fin 8

/-- Explicit list of all AG(3,2) labels. -/
def allAG32Points : List AG32Point := [0, 1, 2, 3, 4, 5, 6, 7]

/-- The `i`-th coordinate of an encoded AG(3,2) point. -/
def agBit (x : AG32Point) (i : Fin 3) : Bool := Nat.testBit x.val i.val

/-- Boolean predicate that the xor of four AG(3,2) labels is zero. -/
def agXor4Zero (a b c d : AG32Point) : Bool :=
  [0, 1, 2].all (fun i : Fin 3 =>
    decide (Bool.xor (Bool.xor (agBit a i) (agBit b i))
      (Bool.xor (agBit c i) (agBit d i)) = false))

/-- Boolean decision predicate for four distinct points whose xor-sum is zero. -/
def isAG32Plane4Bool (a b c d : AG32Point) : Bool :=
  decide (a ≠ b) && decide (a ≠ c) && decide (a ≠ d) &&
  decide (b ≠ c) && decide (b ≠ d) && decide (c ≠ d) && agXor4Zero a b c d

/-- A list of AG(3,2) points contains some four-point affine plane. -/
def containsAG32Plane4List (l : List AG32Point) : Bool :=
  l.any (fun a => l.any (fun b => l.any (fun c => l.any (fun d =>
    isAG32Plane4Bool a b c d))))

/-- All 5-element sublists of the eight AG(3,2) labels contain a four-point affine plane. -/
def allFiveSubsetsContainPlane : Bool :=
  allAG32Points.sublists.all (fun l =>
    if l.length = 5 then containsAG32Plane4List l else true)

/-- Checked finite cap fact used in profile forcing: every five-point subset of
AG(3,2), in the explicit eight-label enumeration, contains a four-point affine
plane.  This kernel-decision statement is kept here in the
profile-forcing namespace so the root file has a local theorem to consume. -/
theorem ag32_cap_five_bool_step47 : allFiveSubsetsContainPlane = true := by
  decide

  /-- In the normalized column coset, the rank-three labels form an affine plane.
  Correct labels: `{1,3,5,7}` (bit 0 set), since `det(base + e₁vᵀ) = v₀` for
  base 272=diag(0,1,1).  Earlier `{0,3,5,6}` was a labeling error;
  the corrected labels above are used in the proof. -/
  theorem normalized_rank_three_labels_form_plane :
      isAG32Plane4Bool (1 : AG32Point) (3 : AG32Point) (5 : AG32Point) (7 : AG32Point) = true := by
    decide

section RankArithmetic

variable {ι : Type*} [Fintype ι]
variable (rk : ι → ℕ)

/-- Number of high-rank factors, i.e. A-rank at least two. -/
def highCount : ℕ := ∑ i : ι, if 2 ≤ rk i then 1 else 0

/-- Number of rank-three factors. -/
def rankThreeCount : ℕ := ∑ i : ι, if rk i = 3 then 1 else 0

/-- Number of rank-two factors. -/
def rankTwoCount : ℕ := ∑ i : ι, if rk i = 2 then 1 else 0

/-- If ranks lie in `{1,2,3}`, then the total rank is the number of terms,
plus one for each high-rank factor, plus one more for each rank-three factor. -/
lemma rank_sum_eq_card_plus_high_plus_rankThree
    (hpos : ∀ i : ι, 1 ≤ rk i) (hupper : ∀ i : ι, rk i ≤ 3) :
    (∑ i : ι, rk i) = Fintype.card ι + highCount rk + rankThreeCount rk := by
  classical
  have hpoint : ∀ i : ι, rk i = 1 ∨ rk i = 2 ∨ rk i = 3 := by
    intro i
    have hp := hpos i
    have hu := hupper i
    omega
  have hterm : ∀ i : ι,
      rk i = 1 + (if 2 ≤ rk i then 1 else 0) + (if rk i = 3 then 1 else 0) := by
    intro i
    rcases hpoint i with h1 | h23
    · simp [h1]
    · rcases h23 with h2 | h3
      · simp [h2]
      · simp [h3]
  calc
    (∑ i : ι, rk i)
        = ∑ i : ι, (1 + (if 2 ≤ rk i then 1 else 0) +
            (if rk i = 3 then 1 else 0)) := by
          apply Finset.sum_congr rfl
          intro i _
          exact hterm i
    _ = Fintype.card ι + highCount rk + rankThreeCount rk := by
          simp [highCount, rankThreeCount, Finset.sum_add_distrib]

/-- High factors split into rank-two and rank-three factors. -/
lemma highCount_eq_rankTwo_add_rankThree
    (hpos : ∀ i : ι, 1 ≤ rk i) (hupper : ∀ i : ι, rk i ≤ 3) :
    highCount rk = rankTwoCount rk + rankThreeCount rk := by
  classical
  have hpoint : ∀ i : ι, rk i = 1 ∨ rk i = 2 ∨ rk i = 3 := by
    intro i
    have hp := hpos i
    have hu := hupper i
    omega
  have hterm : ∀ i : ι,
      (if 2 ≤ rk i then 1 else 0) =
        (if rk i = 2 then 1 else 0) + (if rk i = 3 then 1 else 0) := by
    intro i
    rcases hpoint i with h1 | h23
    · simp [h1]
    · rcases h23 with h2 | h3
      · simp [h2]
      · simp [h3]
  calc
    highCount rk = ∑ i : ι, ((if rk i = 2 then 1 else 0) + (if rk i = 3 then 1 else 0)) := by
      unfold highCount
      apply Finset.sum_congr rfl
      intro i _
      exact hterm i
    _ = rankTwoCount rk + rankThreeCount rk := by
      simp [rankTwoCount, rankThreeCount, Finset.sum_add_distrib]

/-- If 20 nonzero factors have ranks in `{1,2,3}`, total rank at least 27, and
there are at most four high-rank factors, then the exact profile is one rank-two
and three rank-three factors. -/
theorem forced_profile_from_rank_sum_and_high_cap
    (hcard : Fintype.card ι = 20)
    (hpos : ∀ i : ι, 1 ≤ rk i) (hupper : ∀ i : ι, rk i ≤ 3)
    (hrank_sum : 27 ≤ ∑ i : ι, rk i)
    (hhigh_cap : highCount rk ≤ 4)
    (hrank3_cap : rankThreeCount rk ≤ 3) :
    highCount rk = 4 ∧ rankThreeCount rk = 3 ∧ rankTwoCount rk = 1 ∧
      (∑ i : ι, rk i) = 27 := by
  classical
  have hsum_formula := rank_sum_eq_card_plus_high_plus_rankThree rk hpos hupper
  have hhigh_eq := highCount_eq_rankTwo_add_rankThree rk hpos hupper
  have htotal_excess : 7 ≤ highCount rk + rankThreeCount rk := by omega
  have hupper_excess : highCount rk + rankThreeCount rk ≤ 7 := by omega
  have hexcess : highCount rk + rankThreeCount rk = 7 := by omega
  have hhigh_four : highCount rk = 4 := by omega
  have hrt3 : rankThreeCount rk = 3 := by omega
  have hrt2 : rankTwoCount rk = 1 := by omega
  refine ⟨hhigh_four, hrt3, hrt2, ?_⟩
  omega

end RankArithmetic

end QiushiMatmul
