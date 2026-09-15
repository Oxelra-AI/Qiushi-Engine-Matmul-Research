import QiushiHuaCoset

/-!
# Hua sunflower theorem: pairwise rank-one family → coset confinement

Extends `QiushiHuaCoset.lean` (the bitmask kernel facts) with the full
sunflower theorem: a family of nonzero rank-one `3×3` F₂ matrices whose
pairwise sums have rank ≤ 1 shares a common row or column direction.

The proof is **logical** (case analysis + the pairwise kernel fact),
not a large enumeration.
-/

open BigOperators

set_option linter.unusedSectionVars false

namespace QiushiMatmul

/-! ## Family confinement over (Fin 7 × Fin 7) factored rank-one matrices -/

/-- A factored nonzero rank-one 3×3 F₂ matrix. -/
structure RkOneFact where
  u : Fin 7
  v : Fin 7
  deriving DecidableEq

/-- Two factored matrices have pairwise rank-one difference (or are equal). -/
def rk1PairOk (p q : RkOneFact) : Prop :=
  p = q ∨ rankCode (Nat.xor (outerCode p.u p.v) (outerCode q.u q.v)) ≤ 1

/-- The pairwise condition for a list. -/
def PairwiseRk1 (fam : List RkOneFact) : Prop :=
  ∀ p ∈ fam, ∀ q ∈ fam, rk1PairOk p q

/-- All members share a common row direction. -/
def SharesRow (fam : List RkOneFact) : Prop :=
  ∃ u₀ : Fin 7, ∀ p ∈ fam, p.u = u₀

/-- All members share a common column direction. -/
def SharesCol (fam : List RkOneFact) : Prop :=
  ∃ v₀ : Fin 7, ∀ p ∈ fam, p.v = v₀

/-- Helper: extract the rank-one shared-factor from `hua_pairwise_rank_one`. -/
private theorem shared_factor_of_pair (p q : RkOneFact) (hne : p ≠ q)
    (hpair : rk1PairOk p q) : p.u = q.u ∨ p.v = q.v := by
  rcases hpair with heq | hrank
  · exact absurd heq hne
  · have hne_code : outerCode p.u p.v ≠ outerCode q.u q.v := by
      intro hc
      have ⟨hu, hv⟩ := outerCode_injective _ _ _ _ hc
      exact hne (show p = q by cases p; cases q; simp_all)
    exact hua_pairwise_rank_one p.u p.v q.u q.v hne_code hrank

/-- **Family confinement (sunflower).** A pairwise rank-one-difference family
of factored rank-one matrices shares a row or column direction. -/
theorem family_confinement (fam : List RkOneFact) (hpair : PairwiseRk1 fam) :
    SharesRow fam ∨ SharesCol fam := by
  cases fam with
  | nil => exact Or.inl ⟨0, fun _ hp => by cases hp⟩
  | cons p₀ rest =>
    by_cases hall : ∀ q ∈ rest, q.u = p₀.u
    · exact Or.inl ⟨p₀.u, fun r hr => by
        cases hr with
        | head => rfl
        | tail _ hr => exact hall r hr⟩
    · simp only [not_forall, Classical.not_imp] at hall
      obtain ⟨q, hq_mem, hq_u⟩ := hall
      have hq_ne : q ≠ p₀ := fun he => hq_u (he ▸ rfl)
      have hq_share := shared_factor_of_pair q p₀ hq_ne
        (hpair q (List.mem_cons_of_mem p₀ hq_mem) p₀ List.mem_cons_self)
      have hq_v : q.v = p₀.v := by
        rcases hq_share with hu | hv
        · exact absurd hu hq_u
        · exact hv
      refine Or.inr ⟨p₀.v, fun r hr => ?_⟩
      cases hr with
      | head => rfl
      | tail _ hr_mem =>
        by_cases hru : r.u = p₀.u
        · -- r shares row with p₀, so it must share column with q (= p₀'s column)
          have hr_ne_q : r ≠ q := fun he => hq_u (he ▸ hru)
          have hr_share_q := shared_factor_of_pair r q hr_ne_q
            (hpair r (List.mem_cons_of_mem p₀ hr_mem) q (List.mem_cons_of_mem p₀ hq_mem))
          rcases hr_share_q with hu | hv
          · rw [hu] at hru; exact absurd hru hq_u
          · rw [hv, hq_v]
        · -- r doesn't share row with p₀, so it shares column with p₀
          have hr_ne_p : r ≠ p₀ := fun he => hru (he ▸ rfl)
          have hr_share_p := shared_factor_of_pair r p₀ hr_ne_p
            (hpair r (List.mem_cons_of_mem p₀ hr_mem) p₀ List.mem_cons_self)
          rcases hr_share_p with hu | hv
          · exact absurd hu hru
          · exact hv

/-! ## Connection to `outerMat` -/

/-- The nonzero 3-bit vector indexed by `Fin 7` (index `k` → value `k+1`). -/
def vecFromFin7 (k : Fin 7) : I3 → F2 :=
  fun i => if Nat.testBit (k.val + 1) i.val then 1 else 0

/-- Every `vecFromFin7` output is nonzero. -/
theorem vecFromFin7_ne_zero (k : Fin 7) : vecFromFin7 k ≠ 0 := by
  decide +revert

/-- `codeMat (outerCode u v) = outerMat (vecFromFin7 u) (vecFromFin7 v)`. -/
theorem codeMat_outerCode_eq (u v : Fin 7) :
    codeMat (outerCode u v) = outerMat (vecFromFin7 u) (vecFromFin7 v) := by
  decide +revert

/-- Every nonzero 3-component F₂ vector has a `Fin 7` index. -/
theorem vec_has_fin7 (w : I3 → F2) (hw : w ≠ 0) :
    ∃ k : Fin 7, vecFromFin7 k = w := by
  decide +revert

end QiushiMatmul
