import Mathlib

/-!
# Generic Prop-level soundness for branch-tree certificates

This file supplies the missing reusable bridge between a Boolean recursive tree
checker and the semantic statement that an integer branch tree closes every
assignment satisfying a base system.  It is deliberately independent of any
particular orbit or row table.  Later occupation generators should instantiate
`checkLeaf` with their row-reference/Farkas checker and use `no_model_of_checkTree`
rather than proving only that one embedded Boolean certificate evaluates to
`true`.
-/

namespace QiushiMatmul

/-- A branch assumption over an integer occupation variable.  `isUpper = true`
means `x_q ≤ value`; `isUpper = false` means `x_q ≥ value`, encoded as
`-x_q ≤ -value`. -/
structure BranchBound where
  q : Nat
  isUpper : Bool
  value : Int
  deriving Repr, DecidableEq

namespace BranchBound

/-- Semantic interpretation of one branch bound. -/
def Holds (b : BranchBound) (x : Nat → Int) : Prop :=
  if b.isUpper then x b.q ≤ b.value else -x b.q ≤ -b.value

end BranchBound

/-- All branch assumptions accumulated along a path hold for `x`. -/
def ContextHolds (ctx : List BranchBound) (x : Nat → Int) : Prop :=
  ∀ b, b ∈ ctx → b.Holds x

/-- Integer branching is exhaustive: every integer value either satisfies the
upper child `z ≤ k` or the lower child `z ≥ k+1`. -/
theorem integer_split_cover (z k : Int) : z ≤ k ∨ -z ≤ -(k + 1) := by
  omega

lemma context_holds_append_upper {ctx : List BranchBound} {x : Nat → Int} {q : Nat} {floor : Int}
    (hctx : ContextHolds ctx x) (hupper : x q ≤ floor) :
    ContextHolds (ctx ++ [{ q := q, isUpper := true, value := floor }]) x := by
  intro b hb
  rw [List.mem_append] at hb
  rcases hb with hbctx | hbsing
  · exact hctx b hbctx
  · simp at hbsing
    rcases hbsing with rfl
    simp [BranchBound.Holds, hupper]

lemma context_holds_append_lower {ctx : List BranchBound} {x : Nat → Int} {q : Nat} {floor : Int}
    (hctx : ContextHolds ctx x) (hlower : -x q ≤ -(floor + 1)) :
    ContextHolds (ctx ++ [{ q := q, isUpper := false, value := floor + 1 }]) x := by
  intro b hb
  rw [List.mem_append] at hb
  rcases hb with hbctx | hbsing
  · exact hctx b hbctx
  · simp at hbsing
    rcases hbsing with rfl
    change -x q ≤ -(floor + 1)
    exact hlower

/-- Abstract binary integer branch tree.  A leaf carries certificate data of
arbitrary type `α`; the generic theorem below does not inspect that data. -/
inductive BranchTree (α : Type) where
  | leaf : α → BranchTree α
  | branch : Nat → Int → BranchTree α → BranchTree α → BranchTree α
  deriving Repr

/-- Semantic closure of a branch tree relative to a base predicate and a leaf
closure predicate.  At a leaf, the separately proved leaf predicate is required;
at a branch, both children close under complementary integer split contexts. -/
def BranchTreeCloses {α : Type} (leafCloses : List BranchBound → α → Prop) :
    List BranchBound → BranchTree α → Prop
  | ctx, BranchTree.leaf cert => leafCloses ctx cert
  | ctx, BranchTree.branch q floor left right =>
      BranchTreeCloses leafCloses (ctx ++ [{ q := q, isUpper := true, value := floor }]) left ∧
      BranchTreeCloses leafCloses (ctx ++ [{ q := q, isUpper := false, value := floor + 1 }]) right

/-- Generic Boolean recursive checker.  `live q` is a syntactic well-formedness
test for branch variables; semantic soundness below does not require it except
through the Boolean result. -/
def checkTree {α : Type} (live : Nat → Bool)
    (checkLeaf : List BranchBound → α → Bool) :
    List BranchBound → BranchTree α → Bool
  | ctx, BranchTree.leaf cert => checkLeaf ctx cert
  | ctx, BranchTree.branch q floor left right =>
      live q &&
      checkTree live checkLeaf (ctx ++ [{ q := q, isUpper := true, value := floor }]) left &&
      checkTree live checkLeaf (ctx ++ [{ q := q, isUpper := false, value := floor + 1 }]) right

/-- If a Boolean leaf checker implies the Prop-level leaf closure predicate, then
the recursive Boolean tree checker implies Prop-level tree closure. -/
theorem branchTreeCloses_of_checkTree {α : Type}
    (live : Nat → Bool) (checkLeaf : List BranchBound → α → Bool)
    (leafCloses : List BranchBound → α → Prop)
    (hleaf : ∀ ctx cert, checkLeaf ctx cert = true → leafCloses ctx cert) :
    ∀ (ctx : List BranchBound) (tree : BranchTree α),
      checkTree live checkLeaf ctx tree = true → BranchTreeCloses leafCloses ctx tree := by
  intro ctx tree
  induction tree generalizing ctx with
  | leaf cert =>
      intro hcheck
      exact hleaf ctx cert hcheck
  | branch q floor left right ihl ihr =>
      intro hcheck
      cases hleft : checkTree live checkLeaf (ctx ++ [{ q := q, isUpper := true, value := floor }]) left <;>
        cases hright : checkTree live checkLeaf (ctx ++ [{ q := q, isUpper := false, value := floor + 1 }]) right <;>
        simp [checkTree, hleft, hright] at hcheck
      exact ⟨ihl _ hleft, ihr _ hright⟩

/-- A semantically closed branch tree excludes every assignment satisfying the
base system and the inherited branch context, provided closed leaves exclude
such assignments. -/
theorem no_model_of_branchTreeCloses_context {α : Type}
    {base : (Nat → Int) → Prop}
    {leafCloses : List BranchBound → α → Prop}
    (hleaf_sound : ∀ ctx cert, leafCloses ctx cert →
      ∀ x, base x → ContextHolds ctx x → False) :
    ∀ {ctx : List BranchBound} {tree : BranchTree α},
      BranchTreeCloses leafCloses ctx tree →
      ∀ x, base x → ContextHolds ctx x → False := by
  intro ctx tree hclosed
  induction tree generalizing ctx with
  | leaf cert =>
      intro x hbase hctx
      exact hleaf_sound ctx cert hclosed x hbase hctx
  | branch q floor left right ihl ihr =>
      intro x hbase hctx
      rcases hclosed with ⟨hleft, hright⟩
      rcases integer_split_cover (x q) floor with hupper | hlower
      · exact ihl hleft x hbase (context_holds_append_upper hctx hupper)
      · exact ihr hright x hbase (context_holds_append_lower hctx hlower)

/-- Root no-model theorem directly from a checked branch tree.  This is the
bridge later generated orbit certificates should use: after proving the leaf
checker sound once, a per-orbit `by decide` proof of `checkTree ... [] tree =
true` yields semantic infeasibility of the whole integer system. -/
theorem no_model_of_checkTree {α : Type}
    (live : Nat → Bool) (checkLeaf : List BranchBound → α → Bool)
    {base : (Nat → Int) → Prop}
    (leafCloses : List BranchBound → α → Prop)
    (hleaf : ∀ ctx cert, checkLeaf ctx cert = true → leafCloses ctx cert)
    (hleaf_sound : ∀ ctx cert, leafCloses ctx cert →
      ∀ x, base x → ContextHolds ctx x → False)
    {tree : BranchTree α}
    (hcheck : checkTree live checkLeaf [] tree = true) :
    ∀ x, base x → False := by
  intro x hbase
  have hclosed := branchTreeCloses_of_checkTree live checkLeaf leafCloses hleaf [] tree hcheck
  exact no_model_of_branchTreeCloses_context hleaf_sound hclosed x hbase (by
    intro b hb
    simp at hb)

end QiushiMatmul
