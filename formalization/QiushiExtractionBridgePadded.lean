import QiushiExtractionBridge

/-!
# Padded extraction bridge for branch occupation certificates

This module removes the artificial preceding-bound/zero-fiber requirement from the
branch-extraction bridge.  A length `r ≤ T` quotient decomposition may have some
terms in the zero quotient fiber.  The live occupation vector is padded by
`T - (r - x₀)`, where `x₀` is the zero-fiber size.  Since `W ≤ U` for every
occupation source row, the sharp source row bound counts the zero fiber too:
`x₀ + active_live ≤ r - m`.  Padding one live coordinate then preserves every
row bound at target `T`.
-/

set_option maxHeartbeats 8000000

open BigOperators Finset Matrix

attribute [local instance] Classical.propDecidable

noncomputable section

namespace QiushiMatmul

/-- Live occupation vector padded to target length `target`.

The classifier uses label `0` for the killed `W`-coset and labels `1..nLive` for
live quotient labels.  If the original decomposition has length `r` and zero
fiber size `x₀`, its live total is `r-x₀`; the padding amount is
`target - (r-x₀)` and is added to one fixed live coordinate `pad`. -/
def occVectorIntPadded {r nLive : ℕ}
    (classify : Fin r → Fin (nLive + 1)) (target : ℕ) (pad : Fin nLive) :
    Fin nLive → Int :=
  fun j => (occFiberCard' classify (Fin.succ j) : Int) +
    if j = pad then ((target - (r - occFiberCard' classify 0) : Nat) : Int) else 0

private lemma sum_single_if_eq {α : Type*} [Fintype α] [DecidableEq α]
    (pad : α) (d : Int) :
    (∑ j : α, (if j = pad then d else 0)) = d := by
  rw [Finset.sum_eq_single pad]
  · simp
  · intro b _ hb
    simp [hb]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ pad))

private lemma sum_filter_single_if_eq {nLive : ℕ}
    (activeSet : Finset (Fin nLive)) (pad : Fin nLive) (d : Int) :
    (∑ j ∈ activeSet, (if j = pad then d else 0)) =
      if pad ∈ activeSet then d else 0 := by
  by_cases hp : pad ∈ activeSet
  · rw [Finset.sum_eq_single pad]
    · simp [hp]
    · intro b _ hb
      simp [hb]
    · intro hnot
      exact False.elim (hnot hp)
  · calc
      (∑ j ∈ activeSet, (if j = pad then d else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hne : j ≠ pad := by
          intro h
          exact hp (by rwa [h] at hj)
        simp [hne]
      _ = (if pad ∈ activeSet then d else 0) := by simp [hp]

/-- The padded live occupation vector has exact target total when `r ≤ target`. -/
theorem occVectorIntPadded_total {r nLive target : ℕ}
    (classify : Fin r → Fin (nLive + 1)) (pad : Fin nLive) (hrt : r ≤ target) :
    ∑ j : Fin nLive, occVectorIntPadded classify target pad j = (target : Int) := by
  unfold occVectorIntPadded
  rw [Finset.sum_add_distrib]
  rw [sum_single_if_eq pad ((target - (r - occFiberCard' classify 0) : Nat) : Int)]
  have htot := occFiberCard'_total classify
  rw [Fin.sum_univ_succ] at htot
  change occFiberCard' classify 0 +
      (∑ j : Fin nLive, occFiberCard' classify (Fin.succ j)) = r at htot
  have hzero_le : occFiberCard' classify 0 ≤ r := by omega
  have hlive : (∑ j : Fin nLive, occFiberCard' classify (Fin.succ j)) =
      r - occFiberCard' classify 0 := by omega
  have hliveInt : (∑ j : Fin nLive, (occFiberCard' classify (Fin.succ j) : Int)) =
      ((r - occFiberCard' classify 0 : Nat) : Int) := by
    exact_mod_cast hlive
  rw [hliveInt]
  omega

/-- Each padded live occupation coordinate is nonnegative. -/
theorem occVectorIntPadded_nonneg {r nLive target : ℕ}
    (classify : Fin r → Fin (nLive + 1)) (pad : Fin nLive) (j : Fin nLive) :
    0 ≤ occVectorIntPadded classify target pad j := by
  unfold occVectorIntPadded
  by_cases h : j = pad
  · simp [h]
    exact add_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  · simp [h]

private lemma zero_not_mem_succ_image {nLive : ℕ} (activeSet : Finset (Fin nLive)) :
    (0 : Fin (nLive + 1)) ∉ activeSet.image Fin.succ := by
  intro h
  rcases Finset.mem_image.mp h with ⟨j, _hj, hsucc⟩
  have hv : j.val + 1 = 0 := by
    simpa using congrArg Fin.val hsucc
  omega

private lemma sum_insert_zero_image_succ {r nLive : ℕ}
    (classify : Fin r → Fin (nLive + 1)) (activeSet : Finset (Fin nLive)) :
    (∑ label ∈ insert (0 : Fin (nLive + 1)) (activeSet.image Fin.succ),
        occFiberCard' classify label) =
      occFiberCard' classify 0 +
        ∑ j ∈ activeSet, occFiberCard' classify (Fin.succ j) := by
  rw [Finset.sum_insert (zero_not_mem_succ_image activeSet)]
  rw [Finset.sum_image]
  intro a _ b _ h
  exact Fin.succ_injective _ h

/-- Sharp row bound with the zero fiber carried explicitly.

If `W ≤ U`, the zero label is in `U`, and every active live label is in `U`,
then the zero fiber plus the active live fibers are all counted by `killSet D U`.
Thus a source lower bound `m` gives the sharp `≤ r-m` bound before padding. -/
theorem live_labeled_fiber_occ_row_with_zero_nat {W U : Submodule F2 Mat3} (hWU : W ≤ U)
    {r nLive : ℕ} (D : QuotientTensorDecomp W r)
    (classify : Fin r → Fin (nLive + 1))
    (activeSet : Finset (Fin nLive))
    (hzero : ∀ t : Fin r, classify t = 0 → D.A t ∈ U)
    (hcontain : ∀ t : Fin r, classify t ∈ activeSet.image Fin.succ → D.A t ∈ U)
    {m : ℕ} (hm : QuotientRankAtLeast U m) (hmr : m ≤ r) :
    occFiberCard' classify 0 +
      ∑ j ∈ activeSet, occFiberCard' classify (Fin.succ j) ≤ r - m := by
  have hlabels := labeled_fiber_sum_le_killSet hWU D classify
    (insert (0 : Fin (nLive + 1)) (activeSet.image Fin.succ))
    (by
      intro t ht
      simp only [Finset.mem_insert] at ht
      rcases ht with h0 | hact
      · exact hzero t h0
      · exact hcontain t hact)
  rw [sum_insert_zero_image_succ classify activeSet] at hlabels
  exact le_trans hlabels (occupation_inequality hWU D hm hmr)

/-- Padded integer row bound.

This is the row-level engine for padding.  If `m > r`, the source quotient lower
bound already contradicts the decomposition after further quotienting.  If
`m ≤ r`, the sharp bound `zero + active ≤ r-m` and padding amount
`target-(r-zero)` imply the target row bound `active(padded) ≤ target-m`, whether
or not the padded coordinate lies in the active set. -/
theorem live_labeled_fiber_occ_row_int_padded {W U : Submodule F2 Mat3} (hWU : W ≤ U)
    {r nLive : ℕ} (D : QuotientTensorDecomp W r)
    (classify : Fin r → Fin (nLive + 1))
    (activeSet : Finset (Fin nLive))
    (hzero : ∀ t : Fin r, classify t = 0 → D.A t ∈ U)
    (hcontain : ∀ t : Fin r, classify t ∈ activeSet.image Fin.succ → D.A t ∈ U)
    {m : ℕ} (hm : QuotientRankAtLeast U m)
    {target : ℕ} (hrt : r ≤ target) (pad : Fin nLive) :
    (∑ j ∈ activeSet, occVectorIntPadded classify target pad j) ≤
      ((target - m : Nat) : Int) := by
  by_cases hmr : m ≤ r
  · let z : ℕ := occFiberCard' classify 0
    let s : ℕ := ∑ j ∈ activeSet, occFiberCard' classify (Fin.succ j)
    have hsharp : z + s ≤ r - m := by
      dsimp [z, s]
      exact live_labeled_fiber_occ_row_with_zero_nat hWU D classify activeSet hzero hcontain hm hmr
    have htot := occFiberCard'_total classify
    rw [Fin.sum_univ_succ] at htot
    change occFiberCard' classify 0 +
        (∑ j : Fin nLive, occFiberCard' classify (Fin.succ j)) = r at htot
    have hzle : z ≤ r := by dsimp [z]; omega
    unfold occVectorIntPadded
    rw [Finset.sum_add_distrib]
    have hcast : (∑ j ∈ activeSet, (occFiberCard' classify (Fin.succ j) : Int)) = (s : Int) := by
      dsimp [s]
      exact_mod_cast rfl
    rw [hcast]
    have hpad := sum_filter_single_if_eq activeSet pad
      ((target - (r - occFiberCard' classify 0) : Nat) : Int)
    rw [hpad]
    by_cases hp : pad ∈ activeSet
    · simp [hp]
      dsimp [z] at hzle hsharp ⊢
      dsimp [s] at hsharp
      omega
    · simp [hp]
      dsimp [z] at hzle hsharp ⊢
      dsimp [s] at hsharp
      omega
  · have hlt : r < m := by omega
    exact False.elim (quotient_bound_exceeds_length hWU D hm hlt)

end QiushiMatmul
end
