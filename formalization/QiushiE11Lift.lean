import QiushiDefs

/-!
# Constructive lift from the E11 restricted core

The session's E11 core is the restriction obtained by deleting the `A₀₀`
coordinate.  `E11RestrictedDecomp r` records an ordinary CP decomposition of
those eight retained A-slices: its A-factors vanish at `(0,0)`, and its entry
identity is required at every other A-coordinate.  The missing slice is exactly
the sum of the three elementary tensors

`E₀₀ ⊗ E₀ₖ ⊗ E₀ₖ`, for `k = 0,1,2`.

Thus the construction below is a coordinate-level bridge to the canonical
`TensorEntryDecomp` definition, not an assumed lifting premise.
-/

open Matrix BigOperators

namespace QiushiMatmul

/-- Matrix unit `Eᵢⱼ` in the row-major convention used by `tensorEntry`. -/
def matrixUnit3 (i j : I3) : Mat3 :=
  fun i' j' => if i' = i ∧ j' = j then 1 else 0

/-- A decomposition of the eight-slice core obtained by deleting `A₀₀`. -/
structure E11RestrictedDecomp (r : Nat) where
  A : Fin r → Mat3
  B : Fin r → Mat3
  C : Fin r → Mat3
  A_e00_zero : ∀ t : Fin r, A t 0 0 = 0
  restricted_identity : ∀ a b c : Coord9, a ≠ (0, 0) →
    tensorEntry a b c =
      ∑ t : Fin r, A t a.1 a.2 * B t b.1 b.2 * C t c.1 c.2

/-- Append the three elementary summands restoring the deleted `A₀₀` slice. -/
def e11Lift {r : Nat} (D : E11RestrictedDecomp r) :
    TensorEntryDecomp (r + 3) where
  A := Fin.addCases D.A (fun _ => matrixUnit3 0 0)
  B := Fin.addCases D.B (fun k => matrixUnit3 0 k)
  C := Fin.addCases D.C (fun k => matrixUnit3 0 k)
  entry_identity := by
    intro a b c
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right]
    have hcore :
        (∑ t : Fin r,
          D.A t a.1 a.2 * D.B t b.1 b.2 * D.C t c.1 c.2) =
          if a = (0, 0) then 0 else tensorEntry a b c := by
      split_ifs with ha
      · subst a
        apply Finset.sum_eq_zero
        intro t _
        simp [D.A_e00_zero]
      · exact (D.restricted_identity a b c ha).symm
    rw [hcore]
    by_cases ha : a = (0, 0)
    · subst a
      rcases b with ⟨bi, bj⟩
      rcases c with ⟨ci, cj⟩
      fin_cases bi <;> fin_cases bj <;>
        fin_cases ci <;> fin_cases cj <;>
        simp [tensorEntry, matrixUnit3]
    · have htail :
          (∑ x : Fin 3,
            matrixUnit3 0 0 a.1 a.2 *
              matrixUnit3 0 x b.1 b.2 * matrixUnit3 0 x c.1 c.2) = 0 := by
        have ha' : ¬(a.1 = 0 ∧ a.2 = 0) := by
          intro h
          exact ha (Prod.ext h.1 h.2)
        apply Finset.sum_eq_zero
        intro x _
        simp [matrixUnit3, ha']
      simp [ha, htail]

/-- The E11 bridge: rank `r` for the restricted core gives rank `r+3` for
the full `3×3` matrix-multiplication tensor. -/
theorem e11_restricted_lifts_by_three {r : Nat}
    (D : E11RestrictedDecomp r) : Nonempty (TensorEntryDecomp (r + 3)) :=
  ⟨e11Lift D⟩

/-- The target specialization used by a prospective rank-19 E11 search. -/
theorem e11_rank19_gives_full_rank22
    (D : E11RestrictedDecomp 19) : Nonempty (TensorEntryDecomp 22) := by
  simpa using e11_restricted_lifts_by_three D

end QiushiMatmul
