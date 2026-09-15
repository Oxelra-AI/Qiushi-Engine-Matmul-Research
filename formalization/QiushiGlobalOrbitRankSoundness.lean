import QiushiGlobalOrbitCoverage

/-!
The remaining rank-soundness obligation is the representative registry, not
orbit enumeration. Supremum soundness does not require label consistency.
-/

namespace QiushiMatmul.GlobalOrbit

theorem rank_bound_of_orbit_image {table : FrozenOrbitTable} {i : Fin 496}
    {W : Submodule F2 Mat3} {n : Nat} (horbit : table.OrbitImage i W)
    (h : QuotientRankAtLeast (spanCodes (table.basis i)) n) :
    QuotientRankAtLeast W n := by
  obtain ⟨P, Q, ⟨hP⟩, ⟨hQ⟩, flip, rfl⟩ := horbit
  let := hP
  let := hQ
  apply quotientRankAtLeast_action
  cases flip with
  | false => exact h
  | true => exact quotientRankAtLeast_transpose h

/-- Every term of the maximum is a sound rank lower bound, including overlaps. -/
theorem L0_rank_sound_of_representatives (table : FrozenOrbitTable)
    (hrep : ∀ i : Fin 496,
      QuotientRankAtLeast (spanCodes (table.basis i)) (table.lower i))
    (W : Submodule F2 Mat3) : QuotientRankAtLeast W (table.L0 W) := by
  classical
  intro r hr
  constructor
  intro D
  have hle : table.L0 W ≤ r := by
    apply Finset.sup_le
    intro i _
    split_ifs with hi
    · by_contra hn
      exact (rank_bound_of_orbit_image hi (hrep i) r (by omega)).false D
    · exact Nat.zero_le r
  omega

/-- Exact finite obligation for global frozen-L0 soundness; no labels are assumed sound. -/
theorem frozen_L0_rank_sound_iff_representatives :
    (∀ W : Submodule F2 Mat3, QuotientRankAtLeast W (frozenWangTable.L0 W)) ↔
      ∀ i : Fin 496,
        QuotientRankAtLeast (spanCodes (frozenWangTable.basis i))
          (frozenWangTable.lower i) := by
  constructor
  · intro h i r hr
    have hi : frozenWangTable.OrbitImage i (spanCodes (frozenWangTable.basis i)) :=
      (frozen_image_iff i _).mpr (PlaneOrbit.equivalent_refl _)
    exact h _ r (lt_of_lt_of_le hr (frozenWangTable.lower_le_L0 i hi))
  · exact L0_rank_sound_of_representatives frozenWangTable

/-- Coverage supplies an actual representative together with its transported bound. -/
theorem frozen_coverage_with_rank_bound
    (hrep : ∀ i : Fin 496,
      QuotientRankAtLeast (spanCodes (frozenWangTable.basis i))
        (frozenWangTable.lower i)) (W : Submodule F2 Mat3) :
    ∃ i : Fin 496, frozenWangTable.OrbitImage i W ∧
      QuotientRankAtLeast W (frozenWangTable.lower i) := by
  obtain ⟨i, hi⟩ := frozen_coverage W
  exact ⟨i, hi, rank_bound_of_orbit_image hi (hrep i)⟩

end QiushiMatmul.GlobalOrbit
