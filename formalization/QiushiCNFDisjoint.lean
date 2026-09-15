import Mathlib.Tactic
import Std.Sat.CNF.Relabel

/-! A finite family of CNFs sharing only their primary variables. -/

namespace Qiushi.CNF
open Std.Sat

def conjoin {V : Type*} : List (CNF V) -> CNF V
  | [] => .empty
  | f :: fs => f ++ conjoin fs

@[simp] theorem sat_conjoin {V : Type*} (a : V -> Bool) (fs : List (CNF V)) :
    CNF.Sat a (conjoin fs) <-> ∀ f ∈ fs, CNF.Sat a f := by
  induction fs with
  | nil => simp [conjoin]
  | cons f fs ih =>
    simp only [CNF.Sat] at ih
    simp only [conjoin, CNF.Sat, CNF.eval_append, Bool.and_eq_true, ih,
      List.forall_mem_cons]

abbrev SharedVars (P : Type*) {R : Type*} (A : R -> Type*) := Sum P (Sigma A)

def embedCounter {P R : Type*} {A : R -> Type*} (r : R) :
    Sum P (A r) -> SharedVars P A
  | .inl p => .inl p
  | .inr a => .inr ⟨r,a⟩

def sharedAssignment {P R : Type*} {A : R -> Type*}
    (x : P -> Bool) (ys : (r : R) -> A r -> Bool) : SharedVars P A -> Bool
  | .inl p => x p
  | .inr ⟨r,a⟩ => ys r a

theorem shared_comp_embed {P R : Type*} {A : R -> Type*}
    (x : P -> Bool) (ys : (r : R) -> A r -> Bool) (r : R) :
    sharedAssignment x ys ∘ embedCounter r = Sum.elim x (ys r) := by
  funext v
  cases v <;> rfl

theorem auxiliary_blocks_disjoint {P R : Type*} {A : R -> Type*}
    {r s : R} (h : r ≠ s) (a : A r) (b : A s) :
    embedCounter (P := P) r (.inr a) ≠ embedCounter s (.inr b) := by
  intro he
  have hs : (⟨r,a⟩ : Sigma A) = ⟨s,b⟩ := Sum.inr.inj he
  exact h (congrArg Sigma.fst hs)

def familyCNF {P : Type*} {m : Nat} {A : Fin m -> Type*}
    (fs : (r : Fin m) -> CNF (Sum P (A r))) : CNF (SharedVars P A) :=
  conjoin (List.ofFn (fun r => CNF.relabel (embedCounter r) (fs r)))

@[simp] theorem sat_familyCNF {P : Type*} {m : Nat} {A : Fin m -> Type*}
    (fs : (r : Fin m) -> CNF (Sum P (A r))) (a : SharedVars P A -> Bool) :
    CNF.Sat a (familyCNF fs) <->
      forall r, CNF.Sat (a ∘ embedCounter r) (fs r) := by
  rw [familyCNF, sat_conjoin]
  simp [CNF.Sat]

/-- Each counter's existential extension coexists in a single shared assignment. -/
theorem disjoint_extensions_iff {P : Type*} {m : Nat} {A : Fin m -> Type*}
    (fs : (r : Fin m) -> CNF (Sum P (A r))) (x : P -> Bool) :
    (exists a : SharedVars P A -> Bool,
      (forall p, a (.inl p) = x p) ∧ CNF.Sat a (familyCNF fs)) <->
    forall r, exists y : A r -> Bool, CNF.Sat (Sum.elim x y) (fs r) := by
  constructor
  · rintro ⟨a, hx, hs⟩ r
    refine ⟨fun v => a (.inr ⟨r,v⟩), ?_⟩
    have hr := (sat_familyCNF fs a).mp hs r
    have he : a ∘ embedCounter r = Sum.elim x (fun v => a (.inr ⟨r,v⟩)) := by
      funext v
      cases v with
      | inl p => exact hx p
      | inr v => rfl
    rwa [he] at hr
  · intro h
    choose ys hy using h
    refine ⟨sharedAssignment x ys, fun _ => rfl, ?_⟩
    rw [sat_familyCNF]
    intro r
    rw [shared_comp_embed]
    exact hy r

theorem duplicate_cnf {V : Type*} (a : V -> Bool) (f : CNF V) :
    CNF.Sat a (f ++ f) <-> CNF.Sat a f := by simp [CNF.Sat]

theorem omit_satisfied_cnf {V : Type*} (a : V -> Bool) (f g : CNF V)
    (hg : CNF.Sat a g) : CNF.Sat a (f ++ g) <-> CNF.Sat a f := by
  simpa [CNF.Sat, hg] using (show (f.eval a = true ∧ g.eval a = true) <->
    f.eval a = true from and_iff_left hg)

theorem clauses_subset_preserves_sat {V : Type*} (a : V -> Bool) (f g : CNF V)
    (h : ∀ c ∈ f.clauses, c ∈ g.clauses) (hg : CNF.Sat a g) : CNF.Sat a f := by
  simp only [CNF.Sat, CNF.eval, Array.all_eq_true_iff_forall_mem] at hg ⊢
  exact fun c hc => hg c (h c hc)

def dedupCNF {V : Type*} [DecidableEq V] (f : CNF V) : CNF V :=
  ⟨f.clauses.toList.dedup.toArray⟩

theorem sat_dedupCNF {V : Type*} [DecidableEq V] (a : V -> Bool) (f : CNF V) :
    CNF.Sat a (dedupCNF f) <-> CNF.Sat a f := by
  simp only [CNF.Sat, CNF.eval, Array.all_eq_true_iff_forall_mem]
  simp [dedupCNF]

theorem eval_dedup_literals {V : Type*} [DecidableEq V] (a : V -> Bool) (c : CNF.Clause V) :
    CNF.Clause.eval a c.dedup = CNF.Clause.eval a c := by
  apply Bool.eq_iff_iff.mpr
  simp [CNF.Clause.eval, List.any_eq_true]

theorem tautological_clause {V : Type*} (a : V -> Bool) (c : CNF.Clause V) (p : V)
    (hp : (p,true) ∈ c) (hn : (p,false) ∈ c) : CNF.Clause.eval a c = true := by
  unfold CNF.Clause.eval
  apply List.any_eq_true.mpr
  cases h : a p with
  | false => exact ⟨(p,false),hn,by simp [h]⟩
  | true => exact ⟨(p,true),hp,by simp [h]⟩

end Qiushi.CNF
