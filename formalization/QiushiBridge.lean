import QiushiDefs

/-!
# Bridge: entrywise tensor decomposition gives the split-flattened sum

This module uses the canonical definitions from `QiushiDefs`.  Its central
result is the compositional bridge needed to connect the entrywise tensor rank
statement to the split-flattening saturation endpoint.
-/

open Matrix BigOperators

namespace QiushiMatmul

/-- The `Pinv` permutation matrix encodes exactly the tensor entry, under the
natural reindexing `SIdx → Coord9³`. -/
theorem Pinv_eq_tensorEntry (r c : SIdx) :
    Pinv r c = tensorEntry (r.1, c.1) (r.2.1, r.2.2) (c.2.1, c.2.2) := by
  obtain ⟨r1, r21, r22⟩ := r
  obtain ⟨c1, c21, c22⟩ := c
  simp only [Pinv, tensorEntry, sw, Prod.mk.injEq]
  simp only [eq_comm (a := c1) (b := r21)]

/-- **Forward bridge.** Any entrywise decomposition yields
`∑ t, F(Aₜ,Bₜ,Cₜ) = Pinv` in the canonical split-flattening definitions. -/
theorem entrywise_to_split_sum {n : ℕ} (D : TensorEntryDecomp n) :
    ∑ t, F (D.A t) (D.B t) (D.C t) = Pinv := by
  ext r c
  -- `erw` unfolds Mathlib's semireducible `Matrix` to a Pi type for sum evaluation.
  erw [Finset.sum_apply, Finset.sum_apply]
  simp only [F]
  rw [Pinv_eq_tensorEntry]
  exact (D.entry_identity (r.1, c.1) (r.2.1, r.2.2) (c.2.1, c.2.2)).symm

end QiushiMatmul
