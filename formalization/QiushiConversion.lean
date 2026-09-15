import QiushiDefs

/-!
# Conversion: entrywise decompositions induce A-slot quotient decompositions

Over `F₂`, any exact entrywise tensor decomposition gives a quotient
decomposition modulo every A-subspace `W`.  This is the formal bridge behind the
mathematical one-liner `R(T) ≥ R(T/W)`.
-/

open Matrix BigOperators

namespace QiushiMatmul

/-- The quotient smul-sum equals the true A-slice, entry by entry. -/
theorem smul_sum_eq_slice {r : ℕ} (D : TensorEntryDecomp r) (b c : Coord9) :
    (∑ t : Fin r, (D.B t b.1 b.2 * D.C t c.1 c.2) • D.A t) = tensorASlice b c := by
  ext i j
  show (∑ t : Fin r, (D.B t b.1 b.2 * D.C t c.1 c.2) • (D.A t : I3 → I3 → F2)) i j
    = tensorEntry (i,j) b c
  erw [Finset.sum_apply, Finset.sum_apply]
  rw [show (∑ t : Fin r, ((D.B t b.1 b.2 * D.C t c.1 c.2) •
      (D.A t : I3 → I3 → F2)) i j)
      = ∑ t : Fin r, D.A t i j * D.B t b.1 b.2 * D.C t c.1 c.2 from by
        congr 1
        ext t
        erw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul]
        ring]
  exact (D.entry_identity (i,j) b c).symm

/-- **Conversion.** Over `F₂`, any entrywise decomposition gives a quotient
    decomposition modulo any A-subspace. -/
def entrywise_to_quotient {r : ℕ} (D : TensorEntryDecomp r)
    (W : Submodule F2 Mat3) : QuotientTensorDecomp W r where
  A := D.A
  B := D.B
  C := D.C
  quotient_identity := by
    intro b c
    rw [smul_sum_eq_slice D b c]
    have h0 : tensorASlice b c + tensorASlice b c = 0 := by
      ext i j
      exact CharTwo.add_self_eq_zero _
    rw [h0]
    exact W.zero_mem

/-- **Lower-bound transfer.** A quotient lower bound implies the same lower
bound for the full tensor decomposition length. -/
theorem rank_lower_bound_from_quotient {r n : ℕ}
    (D : TensorEntryDecomp r) (W : Submodule F2 Mat3)
    (hW : QuotientRankAtLeast W n) : n ≤ r := by
  by_contra h
  push Not at h
  exact (hW r h).false (entrywise_to_quotient D W)

end QiushiMatmul
