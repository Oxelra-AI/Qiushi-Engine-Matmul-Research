import Mathlib.Tactic
import Std.Sat.CNF.Relabel

/-!
Explicit forward prefix-counter CNF. The three clause families are those of
`add_row_atmost_forward` in the transparent Python encoder, with input positions
zero-based and counter prefix/threshold positions one-based. Auxiliary values
need not be exact thresholds: existential extension is the correctness contract.
-/

namespace Qiushi.CNF
open Std.Sat

def prefixCount (x : Nat -> Bool) : Nat -> Nat
  | 0 => 0
  | i + 1 => prefixCount x i + if x i then 1 else 0

@[simp] theorem prefix_zero (x : Nat -> Bool) : prefixCount x 0 = 0 := rfl
@[simp] theorem prefix_succ (x : Nat -> Bool) (i : Nat) :
    prefixCount x (i+1) = prefixCount x i + if x i then 1 else 0 := rfl

theorem prefix_le (x : Nat -> Bool) (n : Nat) : prefixCount x n <= n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [prefix_succ]; split <;> omega

def thresholds (x : Nat -> Bool) (i j : Nat) : Bool := decide (j <= prefixCount x i)

def Forward (x : Nat -> Bool) (y : Nat -> Nat -> Bool) (n K : Nat) : Prop :=
  forall i, i < n ->
    (x i = true -> y (i+1) 1 = true) ∧
    (i ≠ 0 ->
      (forall j, j < K -> y i (j+1) = true -> y (i+1) (j+1) = true) ∧
      (forall j, j < K-1 -> x i = true -> y i (j+1) = true -> y (i+1) (j+2) = true))

theorem thresholds_forward (x : Nat -> Bool) (n K : Nat) :
    Forward x (thresholds x) n K := by
  intro i _
  simp only [thresholds, decide_eq_true_eq, prefix_succ]
  constructor
  · intro hx; simp [hx]
  · intro _
    constructor
    · intro j _ hj
      apply decide_eq_true_eq.mpr
      split <;> omega
    · intro j _ hx hj
      apply decide_eq_true_eq.mpr
      simp only [hx, ↓reduceIte]
      omega

theorem forward_forces {x : Nat -> Bool} {y : Nat -> Nat -> Bool} {n K : Nat}
    (h : Forward x y n K) (i : Nat) (hi : i <= n) (j : Nat)
    (hj : j < K) (hc : j+1 <= prefixCount x i) : y i (j+1) = true := by
  induction i generalizing j with
  | zero => simp at hc
  | succ i ih =>
    have hs := h i (by omega)
    have hp := prefix_succ x i
    cases hx : x i with
    | false =>
      simp only [hx, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hp
      have hi0 : i ≠ 0 := by intro hz; subst i; simp only [prefix_zero] at hp; omega
      exact (hs.2 hi0).1 j hj (ih (by omega) j hj (by omega))
    | true =>
      cases j with
      | zero => exact hs.1 hx
      | succ j =>
        simp only [hx, ↓reduceIte] at hp
        have hi0 : i ≠ 0 := by intro hz; subst i; simp only [prefix_zero] at hp; omega
        exact (hs.2 hi0).2 j (by omega) hx (ih (by omega) j (by omega) (by omega))

theorem forward_atmost_iff (x : Nat -> Bool) (n k : Nat) :
    (exists y, Forward x y n (k+1) ∧ y n (k+1) = false) <-> prefixCount x n <= k := by
  constructor
  · rintro ⟨y, hy, ht⟩
    by_contra hn
    have hf := forward_forces hy n (by omega) k (by omega) (by omega)
    simp [ht] at hf
  · intro h
    refine ⟨thresholds x, thresholds_forward x n (k+1), ?_⟩
    simp only [thresholds, decide_eq_false_iff_not]
    omega

abbrev CounterVar := Sum Nat (Nat × Nat)

def assign (x : Nat -> Bool) (y : Nat -> Nat -> Bool) : CounterVar -> Bool
  | .inl i => x i
  | .inr (i,j) => y i j

def input (i : Nat) : CounterVar := .inl i
def aux (i j : Nat) : CounterVar := .inr (i,j)

def ofClauses {V : Type*} (cs : List (CNF.Clause V)) : CNF V := ⟨cs.toArray⟩

@[simp] theorem sat_ofClauses {V : Type*} (a : V -> Bool) (cs : List (CNF.Clause V)) :
    CNF.Sat a (ofClauses cs) <-> ∀ c ∈ cs, CNF.Clause.eval a c = true := by
  simp [CNF.Sat, CNF.eval, ofClauses, List.all_eq_true]

def forwardStep (i K : Nat) : List (CNF.Clause CounterVar) :=
  [[(input i, false), (aux (i+1) 1, true)]] ++
  if i = 0 then [] else
    (List.range K).map (fun j => [(aux i (j+1), false), (aux (i+1) (j+1), true)]) ++
    (List.range (K-1)).map (fun j =>
      [(input i, false), (aux i (j+1), false), (aux (i+1) (j+2), true)])

def forwardCNF (n K : Nat) : CNF CounterVar :=
  ofClauses ((List.range n).flatMap (fun i => forwardStep i K))

theorem clause_imp {V : Type*} (a : V -> Bool) (u v : V) :
    CNF.Clause.eval a [(u,false),(v,true)] = true <-> (a u = true -> a v = true) := by
  cases hu : a u <;> cases hv : a v <;> simp [CNF.Clause.eval, hu, hv]

theorem clause_inc {V : Type*} (a : V -> Bool) (u v w : V) :
    CNF.Clause.eval a [(u,false),(v,false),(w,true)] = true <->
      (a u = true -> a v = true -> a w = true) := by
  cases hu : a u <;> cases hv : a v <;> cases hw : a w <;>
    simp [CNF.Clause.eval, hu, hv, hw]

theorem sat_forwardStep (x : Nat -> Bool) (y : Nat -> Nat -> Bool) (i K : Nat) :
    (∀ c ∈ forwardStep i K, CNF.Clause.eval (assign x y) c = true) <->
    (x i = true -> y (i+1) 1 = true) ∧
    (i ≠ 0 ->
      (forall j, j < K -> y i (j+1) = true -> y (i+1) (j+1) = true) ∧
      (forall j, j < K-1 -> x i = true -> y i (j+1) = true -> y (i+1) (j+2) = true)) := by
  by_cases h : i = 0
  · cases hx : x 0 <;> simp [forwardStep, h, assign, input, aux, hx]
  · simp only [forwardStep, if_neg h, List.forall_mem_append,
      List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true,
      List.forall_mem_map, List.mem_range, clause_imp, clause_inc, assign, input, aux]
    simp [h]

theorem sat_forwardCNF (x : Nat -> Bool) (y : Nat -> Nat -> Bool) (n K : Nat) :
    CNF.Sat (assign x y) (forwardCNF n K) <-> Forward x y n K := by
  simp only [forwardCNF, sat_ofClauses, List.mem_flatMap, List.mem_range,
    forall_exists_index, and_imp]
  constructor
  · intro h i hi
    have hs := fun c hc => h c i hi hc
    exact (sat_forwardStep x y i K).mp hs
  · intro h c i hi hc
    exact (sat_forwardStep x y i K).mpr (h i hi) c hc

def atMostCNF (n k : Nat) : CNF CounterVar :=
  (forwardCNF n (k+1)).add [(aux n (k+1), false)]

theorem sat_atMostCNF (x : Nat -> Bool) (y : Nat -> Nat -> Bool) (n k : Nat) :
    CNF.Sat (assign x y) (atMostCNF n k) <->
      Forward x y n (k+1) ∧ y n (k+1) = false := by
  unfold atMostCNF CNF.Sat
  rw [CNF.eval_add, Bool.and_eq_true, ← CNF.sat_def, sat_forwardCNF]
  simp [CNF.Clause.eval, assign, aux, and_comm]

theorem atMostCNF_correct (x : Nat -> Bool) (n k : Nat) :
    (exists y, CNF.Sat (assign x y) (atMostCNF n k)) <-> prefixCount x n <= k := by
  simp only [sat_atMostCNF]
  exact forward_atmost_iff x n k

end Qiushi.CNF
