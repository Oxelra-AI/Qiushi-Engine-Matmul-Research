import QiushiDefs

/-!
# Occupation lemma for A-slot quotient tensor decompositions

If `T/W` has a quotient decomposition of length `r`, and `U ⊇ W`, then the
terms whose A-factor is not killed by the further quotient give a decomposition
of `T/U`.  Therefore at most `r-m` A-factors can lie in `U` whenever `T/U` has
rank at least `m`.
-/

open Matrix BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

namespace QiushiMatmul

/-- Survivor set: indices whose A-factor is not in `U`. -/
def survSet {W : Submodule F2 Mat3} {r : ℕ}
    (D : QuotientTensorDecomp W r) (U : Submodule F2 Mat3) : Finset (Fin r) :=
  Finset.univ.filter (fun t => D.A t ∉ U)

/-- Killed set: indices whose A-factor is in `U`. -/
def killSet {W : Submodule F2 Mat3} {r : ℕ}
    (D : QuotientTensorDecomp W r) (U : Submodule F2 Mat3) : Finset (Fin r) :=
  Finset.univ.filter (fun t => D.A t ∈ U)

/-- The surviving terms satisfy the quotient identity modulo `U`. -/
theorem survivors_identity_in_U
    {W U : Submodule F2 Mat3} (hWU : W ≤ U)
    {r : ℕ} (D : QuotientTensorDecomp W r)
    (b c : Coord9) :
    tensorASlice b c +
      (∑ t ∈ survSet D U,
        (D.B t b.1 b.2 * D.C t c.1 c.2) • D.A t) ∈ U := by
  have hfull := hWU (D.quotient_identity b c)
  have hsplit : (∑ t : Fin r, (D.B t b.1 b.2 * D.C t c.1 c.2) • D.A t) =
      (∑ t ∈ killSet D U, (D.B t b.1 b.2 * D.C t c.1 c.2) • D.A t) +
      (∑ t ∈ survSet D U, (D.B t b.1 b.2 * D.C t c.1 c.2) • D.A t) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  rw [hsplit] at hfull
  have hk : (∑ t ∈ killSet D U, (D.B t b.1 b.2 * D.C t c.1 c.2) • D.A t) ∈ U := by
    apply Submodule.sum_mem
    intro t ht
    exact U.smul_mem _ ((Finset.mem_filter.mp ht).2)
  set ss := ∑ t ∈ survSet D U, (D.B t b.1 b.2 * D.C t c.1 c.2) • D.A t
  set ks := ∑ t ∈ killSet D U, (D.B t b.1 b.2 * D.C t c.1 c.2) • D.A t
  suffices ha : tensorASlice b c + ss + ks ∈ U by
    have := U.sub_mem ha hk
    rwa [add_sub_cancel_right] at this
  convert hfull using 1
  abel

/-- Partition identity: killed terms plus survivor terms are all terms. -/
theorem kill_surv_card_eq
    {W : Submodule F2 Mat3} {r : ℕ}
    (D : QuotientTensorDecomp W r) (U : Submodule F2 Mat3) :
    (killSet D U).card + (survSet D U).card = r := by
  suffices h : (killSet D U).card + (survSet D U).card = Fintype.card (Fin r) by
    rwa [Fintype.card_fin] at h
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext t
    simp only [killSet, survSet, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and, Decidable.em]
  · exact Finset.disjoint_filter.mpr (fun _ _ h hn => hn h)

/-- Construct the further quotient decomposition. -/
def furtherQuotient
    {W U : Submodule F2 Mat3} (hWU : W ≤ U)
    {r : ℕ} (D : QuotientTensorDecomp W r) :
    QuotientTensorDecomp U (survSet D U).card where
  A := fun i => D.A ((survSet D U).equivFin.symm i)
  B := fun i => D.B ((survSet D U).equivFin.symm i)
  C := fun i => D.C ((survSet D U).equivFin.symm i)
  quotient_identity := by
    intro b c
    have h_mem := survivors_identity_in_U hWU D b c
    convert h_mem using 1
    rw [← Finset.sum_coe_sort (survSet D U)]
    congr 1
    exact Fintype.sum_equiv (survSet D U).equivFin.symm _ _ (fun _ => rfl)

/-- **Occupation inequality.** At most `r-m` A-factors can lie in `U`. -/
theorem occupation_inequality
    {W U : Submodule F2 Mat3} (hWU : W ≤ U)
    {r : ℕ} (D : QuotientTensorDecomp W r)
    {m : ℕ} (hm : QuotientRankAtLeast U m) (hmr : m ≤ r) :
    (killSet D U).card ≤ r - m := by
  by_contra h
  push Not at h
  have hpart := kill_surv_card_eq D U
  have h_surv_lt : (survSet D U).card < m := by omega
  exact (hm _ h_surv_lt).false (furtherQuotient hWU D)

end QiushiMatmul
end
