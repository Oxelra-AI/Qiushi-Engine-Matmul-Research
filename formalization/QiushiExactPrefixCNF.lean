import QiushiSequentialCounter

/-! The transparent encoder's reverse clauses and exact-total prefix counter. -/

namespace Qiushi.CNF
open Std.Sat

def previous (y : Nat -> Nat -> Bool) (i j : Nat) : Bool :=
  if j = 0 then true else if i = 0 then false else y i j

@[simp] theorem previous_thresholds (x : Nat -> Bool) (i j : Nat) :
    previous (thresholds x) i j = thresholds x i j := by
  by_cases hj : j = 0
  · simp [previous, hj, thresholds]
  · by_cases hi : i = 0
    · simp [previous, hi, hj, thresholds]
    · simp [previous, hi, hj]

def Reverse (x : Nat -> Bool) (y : Nat -> Nat -> Bool) (n K : Nat) : Prop :=
  forall i, i < n -> forall j, j < K ->
    (y (i+1) (j+1) = true -> previous y i (j+1) = true ∨ x i = true) ∧
    (y (i+1) (j+1) = true -> previous y i (j+1) = true ∨ previous y i j = true)

theorem thresholds_reverse (x : Nat -> Bool) (n K : Nat) :
    Reverse x (thresholds x) n K := by
  intro i _ j _
  constructor
  · intro h
    have hc : j+1 <= prefixCount x (i+1) := of_decide_eq_true h
    rw [prefix_succ] at hc
    simp only [previous_thresholds, thresholds, decide_eq_true_eq]
    by_cases hx : x i = true
    · exact Or.inr hx
    · left
      simpa [hx] using hc
  · intro h
    have hc : j+1 <= prefixCount x (i+1) := of_decide_eq_true h
    rw [prefix_succ] at hc
    simp only [previous_thresholds, thresholds, decide_eq_true_eq]
    by_cases hx : x i = true
    · right
      simp only [hx, ↓reduceIte] at hc
      omega
    · left
      simpa [hx] using hc

theorem reverse_bounds {x : Nat -> Bool} {y : Nat -> Nat -> Bool} {n K : Nat}
    (h : Reverse x y n K) (i : Nat) (hi : i <= n) (hi0 : 0 < i) (j : Nat)
    (hj : j < K) (hy : y i (j+1) = true) : j+1 <= prefixCount x i := by
  induction i generalizing j with
  | zero => omega
  | succ i ih =>
    have hs := h i (by omega) j hj
    by_cases hp : previous y i (j+1) = true
    · have hne : i ≠ 0 := by intro he; simp [previous, he] at hp
      have hp' : y i (j+1) = true := by simpa [previous, hne] using hp
      have hb := ih (by omega) (by omega) j hj hp'
      simp only [prefix_succ]
      split <;> omega
    · have hx := (hs.1 hy).resolve_left hp
      have hm := (hs.2 hy).resolve_left hp
      rw [prefix_succ]
      simp only [hx, ↓reduceIte]
      cases j with
      | zero => omega
      | succ j =>
        have hne : i ≠ 0 := by intro he; simp [previous, he] at hm
        have hm' : y i (j+1) = true := by simpa [previous, hne] using hm
        have hb := ih (by omega) (by omega) j (by omega) hm'
        omega

/-- Constant boundary literals are simplified exactly as in the Python source. -/
def reverseStep (i K : Nat) : List (CNF.Clause CounterVar) :=
  (List.range K).flatMap (fun j =>
    (if i = 0 then [[(aux (i+1) (j+1), false), (input i, true)]]
      else [[(aux (i+1) (j+1), false), (aux i (j+1), true), (input i, true)]]) ++
    if j = 0 then [] else
      if i = 0 then [[(aux (i+1) (j+1), false)]] else
        [[(aux (i+1) (j+1), false), (aux i (j+1), true), (aux i j, true)]])

def reverseCNF (n K : Nat) : CNF CounterVar :=
  ofClauses ((List.range n).flatMap (fun i => reverseStep i K))

theorem clause_or {V : Type*} (a : V -> Bool) (u v w : V) :
    CNF.Clause.eval a [(u,false),(v,true),(w,true)] = true <->
      (a u = true -> a v = true ∨ a w = true) := by
  cases hu : a u <;> cases hv : a v <;> cases hw : a w <;>
    simp [CNF.Clause.eval, hu, hv, hw]

theorem sat_reverseStep (x : Nat -> Bool) (y : Nat -> Nat -> Bool) (i K : Nat) :
    (∀ c ∈ reverseStep i K, CNF.Clause.eval (assign x y) c = true) <->
    forall j, j < K ->
      (y (i+1) (j+1) = true -> previous y i (j+1) = true ∨ x i = true) ∧
      (y (i+1) (j+1) = true -> previous y i (j+1) = true ∨ previous y i j = true) := by
  simp only [reverseStep, List.forall_mem_flatMap, List.mem_range]
  apply forall_congr'
  intro j
  apply forall_congr'
  intro _
  by_cases hi : i = 0 <;> by_cases hj : j = 0
  · subst i; subst j
    cases hx : x 0 <;> cases hy : y 1 1 <;>
      simp [previous, CNF.Clause.eval, assign, input, aux, hx, hy]
  · subst i
    cases hx : x 0 <;> cases hy : y 1 (j+1) <;>
      simp [hj, previous, CNF.Clause.eval, assign, input, aux, hx, hy]
  · simp only [if_neg hi, List.append_nil, List.forall_mem_cons,
      List.not_mem_nil, false_implies, implies_true, and_true, clause_or,
      previous, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte, hj,
      assign, aux, input]
    simp
  · simp only [if_neg hi, if_neg hj, List.forall_mem_append, List.forall_mem_cons,
      List.not_mem_nil, false_implies, implies_true, and_true, clause_or,
      previous, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
      assign, aux, input]

theorem sat_reverseCNF (x : Nat -> Bool) (y : Nat -> Nat -> Bool) (n K : Nat) :
    CNF.Sat (assign x y) (reverseCNF n K) <-> Reverse x y n K := by
  simp only [reverseCNF, sat_ofClauses, List.forall_mem_flatMap, List.mem_range,
    sat_reverseStep, Reverse]

def exactPrefixCNF (n k : Nat) : CNF CounterVar :=
  ((forwardCNF n (k+1) ++ reverseCNF n (k+1)).add [(aux n k,true)]).add
    [(aux n (k+1),false)]

theorem sat_exactPrefixCNF (x : Nat -> Bool) (y : Nat -> Nat -> Bool) (n k : Nat) :
    CNF.Sat (assign x y) (exactPrefixCNF n k) <->
      Forward x y n (k+1) ∧ Reverse x y n (k+1) ∧
        y n k = true ∧ y n (k+1) = false := by
  simp only [exactPrefixCNF, CNF.Sat, CNF.eval_add, CNF.eval_append, Bool.and_eq_true]
  change ((_ ∧ _ ∧ (CNF.Sat (assign x y) (forwardCNF n (k+1)) ∧
    CNF.Sat (assign x y) (reverseCNF n (k+1))))) <-> _
  rw [sat_forwardCNF, sat_reverseCNF]
  simp [CNF.Clause.eval, assign, aux, and_assoc, and_left_comm, and_comm]

/-- `n > 0` excludes the source encoder's unconstrained reserved zero-prefix row. -/
theorem exactPrefixCNF_correct (x : Nat -> Bool) (n k : Nat) (hn : 0 < n) :
    (exists y, CNF.Sat (assign x y) (exactPrefixCNF n k)) <-> prefixCount x n = k := by
  simp only [sat_exactPrefixCNF]
  constructor
  · rintro ⟨y, hf, hr, hlo, hhi⟩
    have hu := (forward_atmost_iff x n k).mp ⟨y,hf,hhi⟩
    cases k with
    | zero => omega
    | succ k =>
      have hl := reverse_bounds hr n (by omega) hn k (by omega) hlo
      omega
  · intro he
    refine ⟨thresholds x, thresholds_forward x n (k+1),
      thresholds_reverse x n (k+1), ?_, ?_⟩ <;> simp [thresholds, he]

end Qiushi.CNF
