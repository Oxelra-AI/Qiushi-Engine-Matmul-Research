import QiushiDefs

/-!
# Drop-term lemma: removing a zero B or C term from a tensor decomposition

If some summand of a `TensorEntryDecomp` has `B t = 0` or `C t = 0`, that
term contributes nothing and can be removed, yielding `TensorEntryDecomp (r-1)`.

Combined with the below-20 exclusion, this licenses `B u ≠ 0` and `C u ≠ 0`
hypotheses for the length-20 saturation endpoint.
-/

open Matrix BigOperators

namespace QiushiMatmul

/-- Given `TensorEntryDecomp (r+1)` with `B t₀ = 0`, construct `TensorEntryDecomp r`
by dropping term `t₀`. -/
def dropTermB {r : ℕ} (D : TensorEntryDecomp (r + 1)) (t₀ : Fin (r + 1))
    (hB : D.B t₀ = 0) : TensorEntryDecomp r where
  A := fun i => D.A (t₀.succAbove i)
  B := fun i => D.B (t₀.succAbove i)
  C := fun i => D.C (t₀.succAbove i)
  entry_identity := by
    intro a b c
    have orig := D.entry_identity a b c
    rw [orig]
    rw [Fin.sum_univ_succAbove _ t₀]
    simp only [hB, Matrix.zero_apply, zero_mul, mul_zero, zero_add]

/-- Given `TensorEntryDecomp (r+1)` with `C t₀ = 0`, construct `TensorEntryDecomp r`. -/
def dropTermC {r : ℕ} (D : TensorEntryDecomp (r + 1)) (t₀ : Fin (r + 1))
    (hC : D.C t₀ = 0) : TensorEntryDecomp r where
  A := fun i => D.A (t₀.succAbove i)
  B := fun i => D.B (t₀.succAbove i)
  C := fun i => D.C (t₀.succAbove i)
  entry_identity := by
    intro a b c
    have orig := D.entry_identity a b c
    rw [orig]
    rw [Fin.sum_univ_succAbove _ t₀]
    simp only [hC, Matrix.zero_apply, mul_zero, zero_add]

/-- Repeated drop: if any `B` or `C` factor is zero, the decomposition length
can be reduced.  Contrapositively, for the minimal decomposition all `B` and
`C` factors are nonzero. -/
theorem nonzero_BC_of_noDecompBelow {r : ℕ} (D : TensorEntryDecomp r)
    (h_no_shorter : ∀ m : ℕ, m < r → TensorEntryDecomp m → False)
    (t : Fin r) : D.B t ≠ 0 ∧ D.C t ≠ 0 := by
  constructor
  · intro hB
    -- D has length r with B t = 0, so we can drop to r-1
    cases r with
    | zero => exact Fin.elim0 t
    | succ n =>
      exact h_no_shorter n (Nat.lt_succ_of_le le_rfl) (dropTermB D t hB)
  · intro hC
    cases r with
    | zero => exact Fin.elim0 t
    | succ n =>
      exact h_no_shorter n (Nat.lt_succ_of_le le_rfl) (dropTermC D t hC)

end QiushiMatmul
