import Mathlib
import QiushiDefs

/-!
# B-slot deletion for arbitrary slice-family decompositions

This is the deletion form of the substitution mechanism behind Wang's
forced-product values.  It deliberately avoids the forced/free counting
form: substitution deletes one active summand and folds all remaining B-slices.
The theorem is stated for an arbitrary slice family `S : β → γ → V`, so it can
later be instantiated in quotient modules, not only for the fixed matrix-
multiplication quotient tensor in `QiushiDefs`.
-/

open BigOperators Finset

attribute [local instance] Classical.propDecidable

namespace QiushiMatmul

variable {β γ V : Type*}
variable [Fintype β] [Fintype γ]
variable [AddCommGroup V] [Module F2 V]

/-- A bilinear decomposition of an arbitrary B/C-sliced family with values in an
`F₂`-module `V`.  It is the equality version of `QuotientTensorDecomp`, intended
for later use with `V = Mat3 ⧸ W` or with finite quotient-coordinate models. -/
structure BSliceFamilyDecomp (S : β → γ → V) (r : ℕ) where
  A : Fin r → V
  B : Fin r → β → F2
  C : Fin r → γ → F2
  identity : ∀ b c, S b c = ∑ t : Fin r, (B t b * C t c) • A t

/-- Fold all B-slices by the selected coordinate `b₀` using the selected
summand's B-linear form as coefficient.  If `D.B t₀ b₀ = 1`, the summand `t₀`
has zero coefficient in every folded slice. -/
def foldedBFamily {S : β → γ → V} {r : ℕ}
    (D : BSliceFamilyDecomp S (r + 1)) (t₀ : Fin (r + 1)) (b₀ : β) : β → γ → V :=
  fun b c => S b c + (D.B t₀ b) • S b₀ c

/-- Over `F₂`, a nonzero scalar is `1`. -/
lemma F2_eq_one_of_ne_zero (x : F2) (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  · exfalso
    exact hx rfl
  · rfl

/-- The basic B-slot deletion step.  From a decomposition of `S` of length
`r+1`, a coordinate `b₀`, and an active summand `t₀` with `B_{t₀}(b₀)≠0`, we
obtain a decomposition of the folded family of length `r` by deleting `t₀` and
replacing each remaining B-linear form by
`B_t(b)+B_{t₀}(b) B_t(b₀)`.  This is the algebraic core of non-A-slot
substitution; iteration plus a fold-uniform flattening bound gives the desired
forced-product lower bounds. -/
def deleteBDecomp {S : β → γ → V} {r : ℕ}
    (D : BSliceFamilyDecomp S (r + 1)) (t₀ : Fin (r + 1)) (b₀ : β)
    (hactive : D.B t₀ b₀ ≠ 0) :
    BSliceFamilyDecomp (foldedBFamily D t₀ b₀) r where
  A := fun i => D.A (t₀.succAbove i)
  B := fun i b => D.B (t₀.succAbove i) b + D.B t₀ b * D.B (t₀.succAbove i) b₀
  C := fun i c => D.C (t₀.succAbove i) c
  identity := by
    intro b c
    unfold foldedBFamily
    have hb₀ : D.B t₀ b₀ = 1 := F2_eq_one_of_ne_zero (D.B t₀ b₀) hactive
    rw [D.identity b c, D.identity b₀ c]
    calc
      (∑ t : Fin (r + 1), (D.B t b * D.C t c) • D.A t) +
          D.B t₀ b • (∑ t : Fin (r + 1), (D.B t b₀ * D.C t c) • D.A t)
          = ∑ t : Fin (r + 1),
              ((D.B t b + D.B t₀ b * D.B t b₀) * D.C t c) • D.A t := by
            rw [Finset.smul_sum, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro t _
            rw [smul_smul, ← add_smul]
            congr 1
            ring
      _ = ∑ i : Fin r,
              ((D.B (t₀.succAbove i) b + D.B t₀ b * D.B (t₀.succAbove i) b₀) *
                D.C (t₀.succAbove i) c) • D.A (t₀.succAbove i) := by
            rw [Fin.sum_univ_succAbove _ t₀]
            have hzero_coeff :
                ((D.B t₀ b + D.B t₀ b * D.B t₀ b₀) * D.C t₀ c) = 0 := by
              rw [hb₀, mul_one, CharTwo.add_self_eq_zero, zero_mul]
            simp [hzero_coeff]

/-- If a slice of an arbitrary B/C-family is nonzero, then some summand is
active at its B-coordinate.  This is the abstract equality-version of the
nonzero-slice step used before deletion. -/
theorem exists_b_active_of_slice_ne_zero {S : β → γ → V} {r : ℕ}
    (D : BSliceFamilyDecomp S r) {b₀ : β} {c₀ : γ}
    (hne : S b₀ c₀ ≠ 0) :
    ∃ t : Fin r, D.B t b₀ ≠ 0 := by
  by_contra hall
  push Not at hall
  have hzero : (∑ t : Fin r, (D.B t b₀ * D.C t c₀) • D.A t) = 0 := by
    apply Finset.sum_eq_zero
    intro t _
    simp [hall t]
  have hid := D.identity b₀ c₀
  rw [hid, hzero] at hne
  exact hne rfl

/-- The theorem-form wrapper used by dependency auditing. -/
theorem exists_deleteBDecomp {S : β → γ → V} {r : ℕ}
    (D : BSliceFamilyDecomp S (r + 1)) (t₀ : Fin (r + 1)) (b₀ : β)
    (hactive : D.B t₀ b₀ ≠ 0) :
    Nonempty (BSliceFamilyDecomp (foldedBFamily D t₀ b₀) r) :=
  ⟨deleteBDecomp D t₀ b₀ hactive⟩

/-- A nonzero selected slice supplies an active summand and hence one legal
B-slot deletion. -/
theorem exists_deleteBDecomp_of_slice_ne_zero {S : β → γ → V} {r : ℕ}
    (D : BSliceFamilyDecomp S (r + 1)) {b₀ : β} {c₀ : γ}
    (hne : S b₀ c₀ ≠ 0) :
    ∃ t₀ : Fin (r + 1), Nonempty (BSliceFamilyDecomp (foldedBFamily D t₀ b₀) r) := by
  obtain ⟨t₀, ht₀⟩ := exists_b_active_of_slice_ne_zero D hne
  exact ⟨t₀, exists_deleteBDecomp D t₀ b₀ ht₀⟩

end QiushiMatmul
