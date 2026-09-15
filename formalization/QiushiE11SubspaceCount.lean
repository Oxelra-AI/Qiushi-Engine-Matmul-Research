import QiushiTailE11ScopeChecks

open Matrix BigOperators
attribute [local instance] Classical.propDecidable Fintype.ofFinite

noncomputable section
namespace QiushiMatmul.E11SubspaceCount

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

abbrev Independent (V : Type*) [AddCommGroup V] [Module F2 V] (k : Nat) :=
  {v : Fin k → V // LinearIndependent F2 v}

abbrev Spaces (V : Type*) [AddCommGroup V] [Module F2 V] (k : Nat) :=
  {S : Submodule F2 V // Module.finrank F2 S = k}

variable (V : Type*) [AddCommGroup V] [Module F2 V] [Finite V]

def forgetFrame {k : Nat} (x : Σ S : Spaces V k, Independent S.val k) :
    Independent V k :=
  ⟨fun i => (x.2.val i : V),
    x.2.property.map' x.1.val.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)⟩

lemma span_forgetFrame {k : Nat} (S : Spaces V k) (v : Independent S.val k) :
    Submodule.span F2 (Set.range (forgetFrame V ⟨S, v⟩).val) = S.val := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact (v.val i).property
  · simpa [S.property] using finrank_span_eq_card (forgetFrame V ⟨S, v⟩).property

theorem forgetFrame_bijective (k : Nat) :
    Function.Bijective (forgetFrame V (k := k)) := by
  constructor
  · rintro ⟨S, v⟩ ⟨T, w⟩ h
    have hS : S = T := by
      apply Subtype.ext
      rw [← span_forgetFrame V S v, ← span_forgetFrame V T w, h]
    cases hS
    congr 1
    apply Subtype.ext
    funext i
    apply Subtype.ext
    exact congrFun (congrArg Subtype.val h) i
  · intro v
    let S : Spaces V k := ⟨Submodule.span F2 (Set.range v.val),
      by simpa using finrank_span_eq_card v.property⟩
    let w : Fin k → S.val := fun i =>
      ⟨v.val i, Submodule.subset_span (Set.mem_range_self i)⟩
    have hw : LinearIndependent F2 w :=
      LinearIndependent.of_comp S.val.subtype v.property
    exact ⟨⟨S, ⟨w, hw⟩⟩, rfl⟩

/-- Every independent tuple has exactly one span, and is a basis of that span. -/
def frameEquiv (k : Nat) :
    (Σ S : Spaces V k, Independent S.val k) ≃ Independent V k :=
  Equiv.ofBijective (forgetFrame V) (forgetFrame_bijective V k)

def frameCount (n k : Nat) : Nat := ∏ i : Fin k, (2 ^ n - 2 ^ i.val)

theorem subspace_count_mul_frameCount {k : Nat} (hk : k ≤ Module.finrank F2 V) :
    Nat.card (Spaces V k) * frameCount k k = frameCount (Module.finrank F2 V) k := by
  have hc : ∀ S : Spaces V k, Nat.card (Independent S.val k) = frameCount k k := by
    intro S
    have h := card_linearIndependent (K := F2) (V := S.val) (k := k)
      (by rw [S.property])
    simpa [Independent, frameCount, F2, S.property] using h
  calc
    Nat.card (Spaces V k) * frameCount k k =
        ∑ S : Spaces V k, Nat.card (Independent S.val k) := by
      simp_rw [hc]
      simp [Nat.card_eq_fintype_card]
    _ = Nat.card (Σ S : Spaces V k, Independent S.val k) := Nat.card_sigma.symm
    _ = Nat.card (Independent V k) := Nat.card_congr (frameEquiv V k)
    _ = frameCount (Module.finrank F2 V) k := by
      simpa [Independent, frameCount, F2] using card_linearIndependent (K := F2) hk

abbrev Q := TailE11Scope.E11Quotient

def e11DimensionCounts : Fin 9 → Nat :=
  ![1, 255, 10795, 97155, 200787, 97155, 10795, 255, 1]

theorem e11_dimension_counts (k : Fin 9) :
    Nat.card (Spaces Q k.val) = e11DimensionCounts k := by
  have h := subspace_count_mul_frameCount Q (k := k.val)
    (by rw [TailE11Scope.e11_quotient_finrank]; omega)
  rw [TailE11Scope.e11_quotient_finrank] at h
  have hnonzero : frameCount k.val k.val ≠ 0 := by
    fin_cases k <;> norm_num [frameCount, Fin.prod_univ_succ]
  have hnumeric : e11DimensionCounts k * frameCount k.val k.val = frameCount 8 k.val := by
    fin_cases k <;> norm_num [frameCount, e11DimensionCounts, Fin.prod_univ_succ]
  exact mul_right_cancel₀ hnonzero (h.trans hnumeric.symm)

/-- Dimension stratification includes both the zero space and the whole space. -/
def e11DimensionEquiv : Submodule F2 Q ≃ Σ k : Fin 9, Spaces Q k.val where
  toFun S := ⟨⟨Module.finrank F2 S, by
    have h := Submodule.finrank_le S
    rw [TailE11Scope.e11_quotient_finrank] at h
    omega⟩, ⟨S, rfl⟩⟩
  invFun x := x.2.val
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨k, hk⟩, S, hS⟩
    dsimp at hS
    subst k
    rfl

theorem e11_all_subspace_count : Nat.card (Submodule F2 Q) = 417199 := by
  rw [Nat.card_congr e11DimensionEquiv, Nat.card_sigma]
  simp_rw [e11_dimension_counts]
  norm_num [e11DimensionCounts, Fin.sum_univ_succ]

theorem e11_nonzero_proper_subspace_count :
    Nat.card {S : Submodule F2 Q // S ≠ ⊥ ∧ S ≠ ⊤} = 417197 := by
  have hbt : (⊥ : Submodule F2 Q) ≠ ⊤ := by
    intro h
    have hd := congrArg (fun S : Submodule F2 Q => Module.finrank F2 S) h
    simp [TailE11Scope.e11_quotient_finrank] at hd
  have hall : Fintype.card (Submodule F2 Q) = 417199 := by
    simpa using e11_all_subspace_count
  have hends : Fintype.card {S : Submodule F2 Q // S = ⊥ ∨ S = ⊤} = 2 := by
    calc
      _ = ({⊥, ⊤} : Finset (Submodule F2 Q)).card :=
        Fintype.card_of_subtype _ (by intro S; simp)
      _ = 2 := by simp [hbt]
  have hproper : Fintype.card {S : Submodule F2 Q // ¬(S = ⊥ ∨ S = ⊤)} = 417197 := by
    rw [Fintype.card_subtype_compl, hall, hends]
  simpa only [not_or, Nat.card_eq_fintype_card] using hproper

/-- A semantic index, not a claim about the ordering or values of a saved Python cache. -/
def e11SubspaceIndex : Fin 417199 ≃ Submodule F2 Q :=
  (Fintype.equivFinOfCardEq (by simpa using e11_all_subspace_count)).symm

theorem e11_subspace_index_complete (S : Submodule F2 Q) :
    ∃! i : Fin 417199, e11SubspaceIndex i = S := by
  refine ⟨e11SubspaceIndex.symm S, e11SubspaceIndex.apply_symm_apply S, ?_⟩
  intro i hi
  exact e11SubspaceIndex.injective (hi.trans (e11SubspaceIndex.apply_symm_apply S).symm)

/-- The correspondence theorem maps every quotient subspace to exactly one full-space row. -/
def e11OccupationIndex : Fin 417199 ≃ Set.Ici lineRank1 :=
  e11SubspaceIndex.trans (Submodule.comapMkQRelIso lineRank1).toEquiv

theorem e11_supermodule_count : Nat.card (Set.Ici lineRank1) = 417199 := by
  rw [← Nat.card_congr (Submodule.comapMkQRelIso lineRank1).toEquiv]
  exact e11_all_subspace_count

theorem e11_occupation_index_complete (U : Submodule F2 Mat3) (hU : lineRank1 ≤ U) :
    ∃! i : Fin 417199, (e11OccupationIndex i).val = U := by
  refine ⟨e11OccupationIndex.symm ⟨U, hU⟩, ?_, ?_⟩
  · exact congrArg Subtype.val (e11OccupationIndex.apply_symm_apply ⟨U, hU⟩)
  · intro i hi
    apply e11OccupationIndex.injective
    rw [e11OccupationIndex.apply_symm_apply]
    exact Subtype.ext hi

/-- Numeric lower bounds remain explicit; completeness does not certify cache values. -/
theorem e11_occupation_surface_sound {r : Nat} (D : QuotientTensorDecomp lineRank1 r)
    (L : Set.Ici lineRank1 → Nat)
    (hL : ∀ U, QuotientRankAtLeast U.val (L U))
    (hLength : ∀ U, L U ≤ r) :
    ∀ i : Fin 417199,
      (killSet D (e11OccupationIndex i).val).card ≤ r - L (e11OccupationIndex i) := by
  intro i
  exact occupation_inequality (e11OccupationIndex i).property D (hL _) (hLength _)

/-- A concrete decoded table can use this after proving that its entries are distinct. -/
theorem e11_decoded_table_complete (table : Fin 417199 → Submodule F2 Q)
    (hinj : Function.Injective table) : Function.Surjective table := by
  exact ((Fintype.bijective_iff_injective_and_card table).mpr
    ⟨hinj, by simpa using e11_all_subspace_count.symm⟩).surjective

end QiushiMatmul.E11SubspaceCount
