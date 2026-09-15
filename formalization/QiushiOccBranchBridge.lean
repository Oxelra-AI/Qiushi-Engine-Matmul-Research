import QiushiOccupationSoundness
import QiushiBranchTreeSoundness

/-!
# Connecting branch-tree soundness to occupation row/Farkas leaves

`QiushiBranchTreeSoundness` proves that a checked binary tree closes a generic
base predicate once checked leaves are known to be semantically impossible.
`QiushiOccupationSoundness` proves that a resolved list of occupation rows plus
branch-bound rows is impossible from a Farkas multiplier.

This file is the missing generic bridge between them.  It translates a tree
context of `BranchBound`s into the branch hypotheses required by
`leaf_infeasible_of_refs`, and packages a Farkas leaf certificate as the leaf
predicate for `no_model_of_checkTree`.
-/

open BigOperators Finset

namespace QiushiMatmul

/-- A row reference that is a branch bound must occur in the current tree
context.  Root occupation rows, the total row, and nonnegativity rows do not
require a branch assumption. -/
def ContextContainsRef {nLive nOcc : ℕ}
    (ctx : List BranchBound) : RowRef nOcc nLive → Prop
  | .occ _ => True
  | .sumGe => True
  | .nonneg _ => True
  | .branchLe j v => ({ q := j.val, isUpper := true, value := v } : BranchBound) ∈ ctx
  | .branchGe j v => ({ q := j.val, isUpper := false, value := v } : BranchBound) ∈ ctx

/-- A leaf's resolved row references are compatible with the branch context. -/
def RefsCoveredByContext {nLive nOcc m : ℕ}
    (ctx : List BranchBound) (refs : Fin m → RowRef nOcc nLive) : Prop :=
  ∀ i : Fin m, ContextContainsRef ctx (refs i)

/-- Compact Farkas leaf data for an occupation system.  The coefficient/RHS
checks remain Prop-level here; generated Boolean checkers can imply
`FarkasLeafCloses` by `decide` in concrete instances. -/
structure FarkasLeafCert (nLive nOcc : ℕ) where
  m : ℕ
  refs : Fin m → RowRef nOcc nLive
  y : Fin m → Nat

/-- Prop-level meaning of a Farkas leaf under a branch context. -/
def FarkasLeafCloses {nLive nOcc : ℕ} (S : OccSys nLive nOcc)
    (ctx : List BranchBound) (cert : FarkasLeafCert nLive nOcc) : Prop :=
  RefsCoveredByContext ctx cert.refs ∧
  (∀ j : Fin nLive,
    (∑ i : Fin cert.m, (cert.y i : Int) * (cert.refs i).resolveCoeff S j) = 0) ∧
  ((∑ i : Fin cert.m, (cert.y i : Int) * (cert.refs i).resolveRhs S) < 0)

/-- A context-covered Farkas leaf excludes every Nat-indexed assignment whose
finite restriction satisfies the occupation root system and whose branch context
holds. -/
theorem farkasLeaf_sound_from_context {nLive nOcc : ℕ}
    (S : OccSys nLive nOcc)
    (ctx : List BranchBound) (cert : FarkasLeafCert nLive nOcc)
    (hclose : FarkasLeafCloses S ctx cert) :
    ∀ x : Nat → Int, S.RootHolds (fun j : Fin nLive => x j.val) →
      ContextHolds ctx x → False := by
  intro x hroot hctx
  rcases hclose with ⟨hcover, hcoeff, hrhs⟩
  exact leaf_infeasible_of_refs S cert.refs cert.y hcoeff hrhs
    (fun j : Fin nLive => x j.val) hroot
    (fun i j v href => by
      have hc := hcover i
      unfold ContextContainsRef at hc
      rw [href] at hc
      have hh := hctx ({ q := j.val, isUpper := true, value := v } : BranchBound) hc
      simpa [BranchBound.Holds] using hh)
    (fun i j v href => by
      have hc := hcover i
      unfold ContextContainsRef at hc
      rw [href] at hc
      have hh := hctx ({ q := j.val, isUpper := false, value := v } : BranchBound) hc
      have hneg : -x j.val ≤ -v := by simpa [BranchBound.Holds] using hh
      omega)

/-- Generic no-model theorem for an occupation system from a checked branch tree
whose leaves imply `FarkasLeafCloses`.  This is the reusable composition point
for generated occupation certificates. -/
theorem occ_no_nat_model_of_checkTree {nLive nOcc : ℕ}
    (S : OccSys nLive nOcc)
    (live : Nat → Bool)
    (checkLeaf : List BranchBound → FarkasLeafCert nLive nOcc → Bool)
    (hleaf : ∀ ctx cert, checkLeaf ctx cert = true → FarkasLeafCloses S ctx cert)
    {tree : BranchTree (FarkasLeafCert nLive nOcc)}
    (hcheck : checkTree live checkLeaf [] tree = true) :
    ∀ x : Nat → Int, S.RootHolds (fun j : Fin nLive => x j.val) → False := by
  exact no_model_of_checkTree live checkLeaf (FarkasLeafCloses S) hleaf
    (fun ctx cert hclose => farkasLeaf_sound_from_context S ctx cert hclose)
    hcheck

end QiushiMatmul
