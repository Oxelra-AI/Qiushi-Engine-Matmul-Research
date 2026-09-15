import Mathlib

/-!
# Occupation system row-resolution soundness

This module provides the reusable semantic bridge from compact branch/Farkas
certificate data to mathematical infeasibility of occupation systems.

The source-visible row semantics lets generated occupation certificates
share a common mathematical interpretation, with contradictions checked against
Prop-level row semantics rather than only against an embedded Boolean evaluator.
-/

open BigOperators Finset

namespace QiushiMatmul

/-- An occupation system with `nLive` variables and `nOcc` root inequality rows.
Each occupation row `i` says `∑_j occCoeff i j * x j ≤ occRhs i`.
The total-sum bound says `target ≤ ∑_j x j`.
Nonnegativity says `∀ j, 0 ≤ x j`. -/
structure OccSys (nLive nOcc : ℕ) where
  occCoeff : Fin nOcc → Fin nLive → Int
  occRhs : Fin nOcc → Int
  target : Int

/-- Root premises: all occupation rows, total bound, and nonnegativity. -/
structure OccSys.RootHolds (S : OccSys nLive nOcc) (x : Fin nLive → Int) : Prop where
  hOcc : ∀ i : Fin nOcc, (∑ j : Fin nLive, S.occCoeff i j * x j) ≤ S.occRhs i
  hTotal : S.target ≤ ∑ j : Fin nLive, x j
  hNonneg : ∀ j : Fin nLive, 0 ≤ x j

/-- Row reference: the five types of inequalities that can appear in a
certificate leaf.  Branch bounds encode inherited tree-path constraints. -/
inductive RowRef (nOcc nLive : ℕ) where
  | occ (i : Fin nOcc)                    -- occupation row i
  | sumGe                                  -- −∑ x ≤ −target
  | nonneg (j : Fin nLive)                -- −x_j ≤ 0
  | branchLe (j : Fin nLive) (v : Int)    -- x_j ≤ v
  | branchGe (j : Fin nLive) (v : Int)    -- −x_j ≤ −v
  deriving DecidableEq

/-- Coefficient vector for a resolved row reference. -/
def RowRef.resolveCoeff (S : OccSys nLive nOcc) :
    RowRef nOcc nLive → Fin nLive → Int
  | .occ i       => S.occCoeff i
  | .sumGe       => fun _ => -1
  | .nonneg j    => fun k => if k = j then -1 else 0
  | .branchLe j _ => fun k => if k = j then 1 else 0
  | .branchGe j _ => fun k => if k = j then -1 else 0

/-- Right-hand side for a resolved row reference. -/
def RowRef.resolveRhs (S : OccSys nLive nOcc) :
    RowRef nOcc nLive → Int
  | .occ i        => S.occRhs i
  | .sumGe        => -S.target
  | .nonneg _     => 0
  | .branchLe _ v => v
  | .branchGe _ v => -v

/-- Indicator sum: `∑ k, (if k = j then s else 0) * x k = s * x j`. -/
lemma indicator_sum {nLive : ℕ} (j : Fin nLive) (s : Int) (x : Fin nLive → Int) :
    (∑ k : Fin nLive, (if k = j then s else (0 : Int)) * x k) = s * x j := by
  simp [Finset.sum_ite_eq', Finset.mem_univ]

/-- Negation sum: `∑ k, (-1) * x k = -(∑ k, x k)`. -/
lemma neg_sum {nLive : ℕ} (x : Fin nLive → Int) :
    (∑ k : Fin nLive, (-1 : Int) * x k) = -(∑ k : Fin nLive, x k) := by
  simp [neg_mul]

/-- Branch bound hypotheses for a leaf.  Each entry says what value the
variable at the given live index is bounded by. -/
structure BranchHyps (nLive : ℕ) where
  leHyps : List (Fin nLive × Int)   -- x j ≤ v
  geHyps : List (Fin nLive × Int)   -- v ≤ x j

/-- A branch hypothesis set holds for assignment `x`. -/
def BranchHyps.Holds {nLive : ℕ} (B : BranchHyps nLive) (x : Fin nLive → Int) : Prop :=
  (∀ p ∈ B.leHyps, x p.1 ≤ p.2) ∧ (∀ p ∈ B.geHyps, p.2 ≤ x p.1)

/-- Master soundness theorem: every resolved row reference gives a valid
inequality under root premises and branch hypotheses. -/
theorem ref_sound {nLive nOcc : ℕ} (S : OccSys nLive nOcc) (ref : RowRef nOcc nLive)
    (x : Fin nLive → Int) (hroot : S.RootHolds x)
    (hle : ∀ (j : Fin nLive) (v : Int),
      ref = .branchLe j v → x j ≤ v)
    (hge : ∀ (j : Fin nLive) (v : Int),
      ref = .branchGe j v → v ≤ x j) :
    (∑ k : Fin nLive, ref.resolveCoeff S k * x k) ≤ ref.resolveRhs S := by
  cases ref with
  | occ i =>
    simp only [RowRef.resolveCoeff, RowRef.resolveRhs]
    exact hroot.hOcc i
  | sumGe =>
    simp only [RowRef.resolveCoeff, RowRef.resolveRhs]
    rw [neg_sum]
    linarith [hroot.hTotal]
  | nonneg j =>
    simp only [RowRef.resolveCoeff, RowRef.resolveRhs]
    rw [indicator_sum]
    linarith [hroot.hNonneg j]
  | branchLe j v =>
    simp only [RowRef.resolveCoeff, RowRef.resolveRhs]
    rw [indicator_sum]
    have := hle j v rfl
    linarith
  | branchGe j v =>
    simp only [RowRef.resolveCoeff, RowRef.resolveRhs]
    rw [indicator_sum]
    have := hge j v rfl
    linarith

/-- Farkas soundness for occupation systems. -/
theorem farkas_leaf_unsat {nLive m : ℕ}
    (A : Fin m → Fin nLive → Int) (b : Fin m → Int)
    (y : Fin m → Nat)
    (hcoeff : ∀ j : Fin nLive, (∑ i : Fin m, (y i : Int) * A i j) = 0)
    (hrhs : (∑ i : Fin m, (y i : Int) * b i) < 0)
    (x : Fin nLive → Int)
    (hrows : ∀ i : Fin m, (∑ j : Fin nLive, A i j * x j) ≤ b i) :
    False := by
  have hle : (∑ i : Fin m, (y i : Int) * (∑ j : Fin nLive, A i j * x j)) ≤
      (∑ i : Fin m, (y i : Int) * b i) :=
    Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hrows i) (by exact_mod_cast Nat.zero_le (y i))
  have hleft : (∑ i : Fin m, (y i : Int) * (∑ j, A i j * x j)) = 0 := by
    calc (∑ i, (y i : Int) * (∑ j, A i j * x j))
        = ∑ i, ∑ j, (y i : Int) * (A i j * x j) := by simp [Finset.mul_sum]
      _ = ∑ j, ∑ i, (y i : Int) * (A i j * x j) := by rw [Finset.sum_comm]
      _ = ∑ j, (∑ i, (y i : Int) * A i j) * x j := by
            apply Finset.sum_congr rfl; intro j _
            rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring
      _ = 0 := by simp [hcoeff]
  linarith

/-- Given a leaf's row reference descriptors, the corresponding resolved
coefficient matrix and RHS, Farkas multipliers, and the root/branch
hypotheses, derive contradiction. -/
theorem leaf_infeasible_of_refs {nLive nOcc m : ℕ}
    (S : OccSys nLive nOcc)
    (refs : Fin m → RowRef nOcc nLive)
    (y : Fin m → Nat)
    (hcoeff : ∀ j : Fin nLive,
      (∑ i : Fin m, (y i : Int) * (refs i).resolveCoeff S j) = 0)
    (hrhs : (∑ i : Fin m, (y i : Int) * (refs i).resolveRhs S) < 0)
    (x : Fin nLive → Int)
    (hroot : S.RootHolds x)
    (hbranch_le : ∀ (i : Fin m) (j : Fin nLive) (v : Int),
      refs i = .branchLe j v → x j ≤ v)
    (hbranch_ge : ∀ (i : Fin m) (j : Fin nLive) (v : Int),
      refs i = .branchGe j v → v ≤ x j) :
    False := by
  have hrows : ∀ i : Fin m,
      (∑ j, (refs i).resolveCoeff S j * x j) ≤ (refs i).resolveRhs S := by
    intro i
    exact ref_sound S (refs i) x hroot
      (fun j v heq => hbranch_le i j v heq)
      (fun j v heq => hbranch_ge i j v heq)
  exact farkas_leaf_unsat _ _ y hcoeff hrhs x hrows

end QiushiMatmul
