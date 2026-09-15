import Mathlib

/-!
# QiushiDefs: shared definitions for the Qiushi formalization

This module is the single source of the tensor, split-flattening, quotient,
and finite-subspace definitions used by the theorem-bearing modules.  Refactoring
all later modules through this file prevents separately compiled theorems from
referring to definitionally different constants.
-/

open Matrix BigOperators

namespace QiushiMatmul

-- ============================================================================
-- Basic type abbreviations
-- ============================================================================

abbrev F2 := ZMod 2
abbrev I3 := Fin 3
abbrev Coord9 := I3 × I3
abbrev Pair9 := I3 × I3
abbrev Mat3 := Matrix I3 I3 F2
abbrev SIdx := I3 × I3 × I3
abbrev SplitMat := Matrix SIdx SIdx F2

-- ============================================================================
-- Canonical tensor and exact entrywise decompositions
-- ============================================================================

/-- Canonical matrix-multiplication tensor entry over `F₂`:
`T[3i+j, 3j'+k, 3i'+k'] = 1` iff `j = j'`, `i = i'`, and `k = k'`.
Equivalently, the associated trilinear form is `tr(A B Cᵀ)`. -/
def tensorEntry (a b c : Coord9) : F2 :=
  if b.1 = a.2 ∧ c.1 = a.1 ∧ c.2 = b.2 then 1 else 0

/-- An entrywise tensor decomposition of the `3×3` matrix-multiplication tensor. -/
structure TensorEntryDecomp (r : ℕ) where
  A : Fin r → Mat3
  B : Fin r → Mat3
  C : Fin r → Mat3
  entry_identity : ∀ a b c : Coord9,
    tensorEntry a b c = ∑ t : Fin r, A t a.1 a.2 * B t b.1 b.2 * C t c.1 c.2

/-- Formal rank lower-bound predicate for the exact tensor. -/
def RankAtLeast (n : ℕ) : Prop := ∀ r : ℕ, TensorEntryDecomp r → n ≤ r

/-- No decomposition with length at most `n`. -/
def NoDecompAtMost (n : ℕ) : Prop := ∀ r : ℕ, r ≤ n → TensorEntryDecomp r → False

-- ============================================================================
-- Split flattening
-- ============================================================================

/-- The index swap induced by the inverse A-split flattening permutation:
`sw(j,i,k)=(i,j,k)`. -/
def sw (x : SIdx) : SIdx := (x.2.1, x.1, x.2.2)

lemma sw_involutive (x : SIdx) : sw (sw x) = x := by
  cases x with
  | mk a yz => cases yz; rfl

lemma sw_injective : Function.Injective sw := by
  intro x y h
  have h2 := congrArg sw h
  simpa [sw_involutive] using h2

/-- Inverse permutation matrix for the A-split flattening. -/
def Pinv : SplitMat := fun u v => if v = sw u then 1 else 0

/-- Split flattening of an elementary tensor `A ⊗ B ⊗ C`. -/
def F (A B C : Mat3) : SplitMat :=
  fun r c => A r.1 c.1 * B r.2.1 r.2.2 * C c.2.1 c.2.2

-- ============================================================================
-- Quotient tensors in the A-slot
-- ============================================================================

/-- The A-slot slice of the matrix-multiplication tensor at fixed B,C coordinates. -/
def tensorASlice (b c : Coord9) : Mat3 :=
  fun i j => tensorEntry (i,j) b c

/-- A length-`r` decomposition of the quotient tensor modulo an A-subspace `W`.
The residual is written with `+` because subtraction equals addition over `F₂`. -/
structure QuotientTensorDecomp (W : Submodule F2 Mat3) (r : ℕ) where
  A : Fin r → Mat3
  B : Fin r → Mat3
  C : Fin r → Mat3
  quotient_identity : ∀ b c : Coord9,
    tensorASlice b c +
      (∑ t : Fin r, (B t b.1 b.2 * C t c.1 c.2) • A t) ∈ W

/-- The quotient tensor modulo `W` has rank at least `n`. -/
def QuotientRankAtLeast (W : Submodule F2 Mat3) (n : ℕ) : Prop :=
  ∀ r : ℕ, r < n → IsEmpty (QuotientTensorDecomp W r)

-- ============================================================================
-- Bit-coded finite subspaces used by the finite certificate layer
-- ============================================================================

/-- A `3×3` matrix from a row-major 9-bit code. -/
def codeMat (n : Nat) : Mat3 :=
  fun i j => if Nat.testBit n (3 * i.val + j.val) then 1 else 0

/-- Span of a finite list of row-major 9-bit matrix codes. -/
def spanCodes (xs : List Nat) : Submodule F2 Mat3 :=
  Submodule.span F2 {M : Mat3 | ∃ n ∈ xs, M = codeMat n}

-- ============================================================================
-- Linear forms for the bilinear-algorithm interpretation
-- ============================================================================

/-- The first linear form of one bilinear-algorithm summand. -/
def leftForm {r : ℕ} (D : TensorEntryDecomp r) (t : Fin r) (X : Mat3) : F2 :=
  ∑ a : Coord9, X a.1 a.2 * D.A t a.1 a.2

/-- The second linear form of one bilinear-algorithm summand. -/
def rightForm {r : ℕ} (D : TensorEntryDecomp r) (t : Fin r) (Y : Mat3) : F2 :=
  ∑ b : Coord9, Y b.1 b.2 * D.B t b.1 b.2

end QiushiMatmul
