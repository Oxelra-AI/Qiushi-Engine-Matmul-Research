import QiushiSliceSpaceFoldUniform

/-!
# From quotient decompositions to finite slice-family decompositions

The forced-product formalization should not use an abstract quotient module when a
small explicit coordinate map is available.  This module gives the reusable
bridge: any linear map `π` out of `Mat3` that annihilates `W` turns a quotient
identity modulo `W` into an equality-valued `BSliceFamilyDecomp` of the canonical
B/C slice family `π ∘ tensorASlice`.
-/

open BigOperators Finset

attribute [local instance] Classical.propDecidable

namespace QiushiMatmul

variable {V : Type*}
variable [AddCommGroup V] [Module F2 V]
lemma moduleF2_add_self_eq_zero (x : V) : x + x = 0 := by
  rw [← two_smul F2 x]
  have h2 : (2 : F2) = 0 := by decide
  rw [h2, zero_smul]

/-- Applying a linear map that kills `W` to a quotient decomposition gives an
ordinary B/C slice-family decomposition with values in the target module.  Full
rank or surjectivity of `π` is not required for soundness; only `π(W)=0` is used.
-/
def quotientToBSliceFamilyDecomp {W : Submodule F2 Mat3} {r : ℕ}
    (π : Mat3 →ₗ[F2] V)
    (hπW : ∀ X : Mat3, X ∈ W → π X = 0)
    (D : QuotientTensorDecomp W r) :
    BSliceFamilyDecomp (fun b c : Coord9 => π (tensorASlice b c)) r where
  A := fun t => π (D.A t)
  B := fun t b => D.B t b.1 b.2
  C := fun t c => D.C t c.1 c.2
  identity := by
    intro b c
    let Rsum : V := ∑ t : Fin r, (D.B t b.1 b.2 * D.C t c.1 c.2) • π (D.A t)
    have hkill : π (tensorASlice b c +
        (∑ t : Fin r, (D.B t b.1 b.2 * D.C t c.1 c.2) • D.A t)) = 0 :=
      hπW _ (D.quotient_identity b c)
    have hsum :
        π (∑ t : Fin r, (D.B t b.1 b.2 * D.C t c.1 c.2) • D.A t) = Rsum := by
      unfold Rsum
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro t _
      rw [map_smul]
    have hadd : π (tensorASlice b c) + Rsum = 0 := by
      simpa [map_add, hsum] using hkill
    calc π (tensorASlice b c)
        = π (tensorASlice b c) + 0 := by simp
      _ = π (tensorASlice b c) + (Rsum + Rsum) := by
            rw [show Rsum + Rsum = 0 from moduleF2_add_self_eq_zero Rsum]
      _ = (π (tensorASlice b c) + Rsum) + Rsum := by
            abel
      _ = 0 + Rsum := by
            rw [hadd]
      _ = ∑ t : Fin r, (D.B t b.1 b.2 * D.C t c.1 c.2) • π (D.A t) := by
            simp [Rsum]

/-- Applying a linear map that kills `W` to a quotient decomposition, then
swapping the two exterior directions, gives a decomposition of the canonical
C-axis slice family `(b,c) ↦ π(tensorASlice c b)`.  This is the bridge needed
for forced-product seeds whose deletion is naturally in the C-slot: after
swapping B and C, the generic B-deletion theorem applies without duplicating
substitution algebra. -/
def quotientToSwappedBSliceFamilyDecomp {W : Submodule F2 Mat3} {r : ℕ}
    (π : Mat3 →ₗ[F2] V)
    (hπW : ∀ X : Mat3, X ∈ W → π X = 0)
    (D : QuotientTensorDecomp W r) :
    BSliceFamilyDecomp (fun b c : Coord9 => π (tensorASlice c b)) r := by
  let D0 : BSliceFamilyDecomp (fun b c : Coord9 => π (tensorASlice b c)) r :=
    quotientToBSliceFamilyDecomp π hπW D
  exact swapBSliceFamilyDecomp D0

/-- No-short-decomposition transfer form: a slice-family obstruction for
`π ∘ tensorASlice` gives a quotient-rank lower bound for `W`. -/
theorem quotientRankAtLeast_of_sliceFamily_no_short {W : Submodule F2 Mat3} {n : ℕ}
    (π : Mat3 →ₗ[F2] V)
    (hπW : ∀ X : Mat3, X ∈ W → π X = 0)
    (hNo : ∀ r : ℕ, r < n →
      BSliceFamilyDecomp (fun b c : Coord9 => π (tensorASlice b c)) r → False) :
    QuotientRankAtLeast W n := by
  intro r hr
  refine ⟨?_⟩
  intro D
  exact hNo r hr (quotientToBSliceFamilyDecomp π hπW D)

/-- Swapped no-short-decomposition transfer form: a slice-family obstruction for
`(b,c) ↦ π(tensorASlice c b)` gives the same quotient-rank lower bound for
`W`.  This is not a transpose action on the A-subspace; it is only a swap of
the two exterior coordinates inside the quotient-to-slice-family equality. -/
theorem quotientRankAtLeast_of_swapped_sliceFamily_no_short {W : Submodule F2 Mat3} {n : ℕ}
    (π : Mat3 →ₗ[F2] V)
    (hπW : ∀ X : Mat3, X ∈ W → π X = 0)
    (hNo : ∀ r : ℕ, r < n →
      BSliceFamilyDecomp (fun b c : Coord9 => π (tensorASlice c b)) r → False) :
    QuotientRankAtLeast W n := by
  intro r hr
  refine ⟨?_⟩
  intro D
  exact hNo r hr (quotientToSwappedBSliceFamilyDecomp π hπW D)

end QiushiMatmul
