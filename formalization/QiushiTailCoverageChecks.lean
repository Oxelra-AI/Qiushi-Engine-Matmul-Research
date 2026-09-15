import QiushiTail

open Matrix BigOperators
attribute [local instance] Classical.propDecidable

noncomputable section
namespace QiushiMatmul.TailCoverage

def zeroExcessProfiles (rk : Fin 22 → Nat) : Prop :=
  (rankOneCount rk = 17 ∧ rankTwoCount rk = 5 ∧ rankThreeCount rk = 0) ∨
  (rankOneCount rk = 18 ∧ rankTwoCount rk = 3 ∧ rankThreeCount rk = 1)

theorem length22_B_profiles (D : TensorEntryDecomp 22)
    (hA : ∀ t, D.A t ≠ 0) (hB : ∀ t, D.B t ≠ 0)
    (hC : ∀ t, D.C t ≠ 0)
    (hrank : (∑ t, (D.B t).rank) = 27) :
    zeroExcessProfiles (fun t => (D.B t).rank) := by
  apply length22_zero_A_excess_profiles (cycleEntryDecomp D) hB
  · intro t
    simpa using hC t
  · intro t
    simpa using hA t
  · simpa using hrank

theorem length22_C_profiles (D : TensorEntryDecomp 22)
    (hA : ∀ t, D.A t ≠ 0) (hB : ∀ t, D.B t ≠ 0)
    (hC : ∀ t, D.C t ≠ 0)
    (hrank : (∑ t, (D.C t).rank) = 27) :
    zeroExcessProfiles (fun t => (D.C t).rank) := by
  have h := length22_zero_A_excess_profiles
    (cycleEntryDecomp (cycleEntryDecomp D))
    (by intro t; simpa using hC t)
    (by intro t; simpa using hA t)
    (by intro t; simpa using hB t)
    (by simpa using hrank)
  simpa [zeroExcessProfiles] using h

theorem all_slot_split_bounds {r : Nat} (D : TensorEntryDecomp r) :
    (27 ≤ ∑ t, (D.A t).rank) ∧
    (27 ≤ ∑ t, (D.B t).rank) ∧
    (27 ≤ ∑ t, (D.C t).rank) :=
  ⟨split_rank_bound_from_entrywise D, split_rank_bound_B D, split_rank_bound_C D⟩

theorem length21_all_line_cap (P : FinitePremises)
    (D : TensorEntryDecomp 21) (M : Mat3) (hM : M ≠ 0) :
    (Finset.univ.filter fun t => D.A t ∈ Submodule.span F2 {M}).card ≤ 2 := by
  simpa using length21_full_A_occupation_cap D _ (nonzero_line_lb19 P M hM)
    (by decide : 19 ≤ 21)

theorem length21_all_high_pair_plane_cap (P : FinitePremises)
    (D : TensorEntryDecomp 21) (A B : Mat3)
    (hA : 2 ≤ A.rank) (hB : 2 ≤ B.rank) (hAB : 2 ≤ (A + B).rank) :
    (Finset.univ.filter fun t =>
      D.A t ∈ Submodule.span F2 ({A, B} : Set Mat3)).card ≤ 2 := by
  simpa using length21_full_A_occupation_cap D _
    (allHighPlane_pair_lb19 P A B hA hB hAB) (by decide : 19 ≤ 21)

private theorem e11_code_off_coordinate : ∀ a : Coord9,
    a ≠ (0, 0) → codeMat 1 a.1 a.2 = 0 := by
  decide

lemma e11_line_off_coordinate (M : Mat3) (hM : M ∈ lineRank1)
    (a : Coord9) (ha : a ≠ (0, 0)) : M a.1 a.2 = 0 := by
  have hspan : spanCodes [1] = Submodule.span F2 {codeMat 1} := by
    unfold spanCodes
    congr 1
    ext X
    simp
  rw [lineRank1, hspan] at hM
  rcases Submodule.mem_span_singleton.mp hM with ⟨c, rfl⟩
  simp [e11_code_off_coordinate a ha]

/-- Select the coordinate complement of the actual quotient by spanCodes [1]. -/
def e11QuotientToRestricted {r : Nat} (D : QuotientTensorDecomp lineRank1 r) :
    E11RestrictedDecomp r where
  A := fun t i j => if (i, j) = (0, 0) then 0 else D.A t i j
  B := D.B
  C := D.C
  A_e00_zero := by intro t; simp
  restricted_identity := by
    intro a b c ha
    have h := e11_line_off_coordinate _ (D.quotient_identity b c) a ha
    simp only [Matrix.add_apply, tensorASlice, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul] at h
    have heq : tensorEntry a b c =
        ∑ t, D.A t a.1 a.2 * D.B t b.1 b.2 * D.C t c.1 c.2 := by
      have hneg := eq_neg_of_add_eq_zero_left h
      simpa [neg_eq_self, mul_comm, mul_left_comm, mul_assoc] using hneg
    simpa [ha] using heq

theorem e11_quotient_lifts_by_three {r : Nat}
    (D : QuotientTensorDecomp lineRank1 r) : Nonempty (TensorEntryDecomp (r + 3)) :=
  e11_restricted_lifts_by_three (e11QuotientToRestricted D)

theorem e11_quotient_rank19_gives_full_rank22
    (D : QuotientTensorDecomp lineRank1 19) : TensorEntryRankAtMost 22 :=
  e11_rank19_gives_full_rank22 (e11QuotientToRestricted D)

end QiushiMatmul.TailCoverage
