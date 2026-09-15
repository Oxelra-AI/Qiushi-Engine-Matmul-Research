import QiushiTailCoverageChecks

open Matrix BigOperators
attribute [local instance] Classical.propDecidable

noncomputable section
namespace QiushiMatmul.TailPadded

def dropTermA {r : Nat} (D : TensorEntryDecomp (r + 1))
    (t : Fin (r + 1)) (hA : D.A t = 0) : TensorEntryDecomp r where
  A := fun i => D.A (t.succAbove i)
  B := fun i => D.B (t.succAbove i)
  C := fun i => D.C (t.succAbove i)
  entry_identity := by
    intro a b c
    rw [D.entry_identity, Fin.sum_univ_succAbove _ t]
    simp [hA]

theorem zero_A_excess_B_zero_imp_A_zero {r : Nat} (D : TensorEntryDecomp r)
    (hrank : (∑ t, (D.A t).rank) = 27) (t : Fin r) (hB : D.B t = 0) :
    D.A t = 0 := by
  cases r with
  | zero => exact Fin.elim0 t
  | succ n =>
    have hbound := split_rank_bound_from_entrywise (dropTermB D t hB)
    change 27 ≤ ∑ i : Fin n, (D.A (t.succAbove i)).rank at hbound
    rw [Fin.sum_univ_succAbove _ t] at hrank
    by_contra hA
    have hpos := tail_matrix_rank_positive _ hA
    omega

theorem zero_A_excess_C_zero_imp_A_zero {r : Nat} (D : TensorEntryDecomp r)
    (hrank : (∑ t, (D.A t).rank) = 27) (t : Fin r) (hC : D.C t = 0) :
    D.A t = 0 := by
  cases r with
  | zero => exact Fin.elim0 t
  | succ n =>
    have hbound := split_rank_bound_from_entrywise (dropTermC D t hC)
    change 27 ≤ ∑ i : Fin n, (D.A (t.succAbove i)).rank at hbound
    rw [Fin.sum_univ_succAbove _ t] at hrank
    by_contra hA
    have hpos := tail_matrix_rank_positive _ hA
    omega

theorem zero_A_excess_active_BC {r : Nat} (D : TensorEntryDecomp r)
    (hrank : (∑ t, (D.A t).rank) = 27) (t : Fin r) (hA : D.A t ≠ 0) :
    D.B t ≠ 0 ∧ D.C t ≠ 0 :=
  ⟨fun h => hA (zero_A_excess_B_zero_imp_A_zero D hrank t h),
   fun h => hA (zero_A_excess_C_zero_imp_A_zero D hrank t h)⟩

/-- Zero A-factors cause no rank loss, so padded terms do not obstruct saturation. -/
theorem zero_A_excess_saturation {r : Nat} (D : TensorEntryDecomp r)
    (hrank : (∑ t, (D.A t).rank) = 27) :
    ∀ t s, F (D.A t) (D.B t) (D.C t) * Pinv * F (D.A s) (D.B s) (D.C s) =
      if t = s then F (D.A s) (D.B s) (D.C s) else 0 := by
  apply split_flattening_saturation_identities D.A D.B D.C (entrywise_to_split_sum D)
  change (∑ t, (F (D.A t) (D.B t) (D.C t)).rank) = Fintype.card SIdx
  have hpoint : ∀ t, (F (D.A t) (D.B t) (D.C t)).rank = (D.A t).rank := by
    intro t
    by_cases hA : D.A t = 0
    · have hz : F (D.A t) (D.B t) (D.C t) = 0 := by
        ext i j
        simp [QiushiMatmul.F, hA]
      rw [hz, hA]
      simp
    · have hBC := zero_A_excess_active_BC D hrank t hA
      exact F_rank_eq_A_rank _ _ _ hBC.1 hBC.2
  simp_rw [hpoint]
  simpa using hrank

theorem zero_A_excess_at_most_one_invertible {r : Nat} (D : TensorEntryDecomp r)
    (hrank : (∑ t, (D.A t).rank) = 27) :
    ∀ t s, (D.A t).det ≠ 0 → (D.A s).det ≠ 0 → t = s := by
  intro t s hAt hAs
  by_contra hts
  have hAt0 : D.A t ≠ 0 := by intro h; simp [h] at hAt
  have hAs0 : D.A s ≠ 0 := by intro h; simp [h] at hAs
  have htBC := zero_A_excess_active_BC D hrank t hAt0
  have hsBC := zero_A_excess_active_BC D hrank s hAs0
  have hsat := zero_A_excess_saturation D hrank
  have hd_t := diagonal_equation (D.A t) (D.B t) (D.C t) htBC.1 htBC.2
    (by simpa using hsat t t)
  have hd_s := diagonal_equation (D.A s) (D.B s) (D.C s) hsBC.1 hsBC.2
    (by simpa using hsat s s)
  have ho := off_diagonal_equation (D.A t) (D.B t) (D.C t)
    (D.A s) (D.B s) (D.C s) htBC.1 hsBC.2 (by simpa [hts] using hsat t s)
  exact two_invertible_A_factors_contradict_saturation_endpoint
    _ _ _ _ _ _ hAt hAs hd_t hd_s ho

theorem zero_B_excess_at_most_one_invertible {r : Nat} (D : TensorEntryDecomp r)
    (hrank : (∑ t, (D.B t).rank) = 27) :
    ∀ t s, (D.B t).det ≠ 0 → (D.B s).det ≠ 0 → t = s := by
  exact zero_A_excess_at_most_one_invertible (cycleEntryDecomp D) hrank

theorem zero_C_excess_at_most_one_invertible {r : Nat} (D : TensorEntryDecomp r)
    (hrank : (∑ t, (D.C t).rank) = 27) :
    ∀ t s, (D.C t).det ≠ 0 → (D.C s).det ≠ 0 → t = s := by
  have h := zero_A_excess_at_most_one_invertible
    (cycleEntryDecomp (cycleEntryDecomp D)) (by simpa using hrank)
  simpa using h

theorem zero_A_excess_rankThreeCount_le_one {r : Nat} (D : TensorEntryDecomp r)
    (hrank : (∑ t, (D.A t).rank) = 27) :
    rankThreeCount (fun t => (D.A t).rank) ≤ 1 := by
  let T : Finset (Fin r) := Finset.univ.filter fun t => (D.A t).rank = 3
  have hT : T.card = rankThreeCount (fun t => (D.A t).rank) := by
    simp [T, rankThreeCount]
  rw [← hT]
  apply Finset.card_le_one.mpr
  intro t ht s hs
  exact zero_A_excess_at_most_one_invertible D hrank t s
    (tail_det_ne_zero_of_rank_three _ (Finset.mem_filter.mp ht).2)
    (tail_det_ne_zero_of_rank_three _ (Finset.mem_filter.mp hs).2)

theorem length22_A_profiles_of_nonzero_A (D : TensorEntryDecomp 22)
    (hrank : (∑ t, (D.A t).rank) = 27) (hA : ∀ t, D.A t ≠ 0) :
    TailCoverage.zeroExcessProfiles (fun t => (D.A t).rank) := by
  exact length22_zero_A_excess_profiles D hA
    (fun t => (zero_A_excess_active_BC D hrank t (hA t)).1)
    (fun t => (zero_A_excess_active_BC D hrank t (hA t)).2) (by simpa using hrank)

theorem length22_B_profiles_of_nonzero_B (D : TensorEntryDecomp 22)
    (hrank : (∑ t, (D.B t).rank) = 27) (hB : ∀ t, D.B t ≠ 0) :
    TailCoverage.zeroExcessProfiles (fun t => (D.B t).rank) :=
  length22_A_profiles_of_nonzero_A (cycleEntryDecomp D) hrank hB

theorem length22_C_profiles_of_nonzero_C (D : TensorEntryDecomp 22)
    (hrank : (∑ t, (D.C t).rank) = 27) (hC : ∀ t, D.C t ≠ 0) :
    TailCoverage.zeroExcessProfiles (fun t => (D.C t).rank) := by
  have h := length22_A_profiles_of_nonzero_A
    (cycleEntryDecomp (cycleEntryDecomp D))
    (by simpa using hrank) (by intro t; simpa using hC t)
  simpa [TailCoverage.zeroExcessProfiles] using h

theorem length22_A_profiles_of_nonzero_summands (D : TensorEntryDecomp 22)
    (hrank : (∑ t, (D.A t).rank) = 27)
    (hterms : ∀ t, F (D.A t) (D.B t) (D.C t) ≠ 0) :
    TailCoverage.zeroExcessProfiles (fun t => (D.A t).rank) := by
  apply length22_A_profiles_of_nonzero_A D hrank
  intro t ht
  apply hterms t
  ext i j
  simp [QiushiMatmul.F, ht]

/-- A rank lower bound can exclude deleting a term only at that bound's own length. -/
theorem nonzero_A_of_rank_lower_bound {r : Nat} (D : TensorEntryDecomp r)
    (hlower : RankAtLeast r) : ∀ t, D.A t ≠ 0 := by
  intro t ht
  cases r with
  | zero => exact Fin.elim0 t
  | succ n =>
    have h := hlower n (dropTermA D t ht)
    omega

/-- Here the lower bound is part of the meaning of exact rank 22, not supplied by rank >= 21. -/
theorem exact_rank22_A_profiles (D : TensorEntryDecomp 22)
    (hexact : RankAtLeast 22) (hrank : (∑ t, (D.A t).rank) = 27) :
    TailCoverage.zeroExcessProfiles (fun t => (D.A t).rank) :=
  length22_A_profiles_of_nonzero_A D hrank (nonzero_A_of_rank_lower_bound D hexact)

/-- The genuinely weaker padded interface retains the possible 21-term endpoint. -/
theorem length22_A_profiles_or_zero_excess_length21 (D : TensorEntryDecomp 22)
    (hrank : (∑ t, (D.A t).rank) = 27) :
    TailCoverage.zeroExcessProfiles (fun t => (D.A t).rank) ∨
      ∃ E : TensorEntryDecomp 21, (∑ t, (E.A t).rank) = 27 := by
  by_cases hA : ∀ t, D.A t ≠ 0
  · exact Or.inl (length22_A_profiles_of_nonzero_A D hrank hA)
  · push Not at hA
    obtain ⟨t, ht⟩ := hA
    refine Or.inr ⟨dropTermA D t ht, ?_⟩
    change (∑ i, (D.A (t.succAbove i)).rank) = 27
    rw [Fin.sum_univ_succAbove _ t] at hrank
    simpa [ht] using hrank

theorem padded_length22_reduces_to_minimal21 (D : TensorEntryDecomp 22)
    (hlower : RankAtLeast 21) (hrank : (∑ t, (D.A t).rank) = 27)
    (hzero : ∃ t, D.A t = 0) :
    ∃ E : TensorEntryDecomp 21, (∑ t, (E.A t).rank) = 27 ∧
      (∀ t, E.A t ≠ 0) ∧ (∀ t, E.B t ≠ 0) ∧ (∀ t, E.C t ≠ 0) := by
  obtain ⟨t, ht⟩ := hzero
  let E := dropTermA D t ht
  have hE : (∑ t, (E.A t).rank) = 27 := by
    change (∑ i, (D.A (t.succAbove i)).rank) = 27
    rw [Fin.sum_univ_succAbove _ t] at hrank
    simpa [ht] using hrank
  have hA := nonzero_A_of_rank_lower_bound E hlower
  exact ⟨E, hE, hA,
    fun t => (zero_A_excess_active_BC E hE t (hA t)).1,
    fun t => (zero_A_excess_active_BC E hE t (hA t)).2⟩

end QiushiMatmul.TailPadded
