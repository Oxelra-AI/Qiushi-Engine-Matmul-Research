import QiushiBooleanCopies
import QiushiSequentialCounter
import QiushiCNFDisjoint

namespace Qiushi.CNF
open Std.Sat BigOperators

theorem prefix_sum (x : Nat -> Bool) (n : Nat) :
    prefixCount x n = ∑ i ∈ Finset.range n, bit (x i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prefix_succ, Finset.sum_range_succ, ih]
    rfl

theorem prefix_complement (x : Nat -> Bool) (n : Nat) :
    prefixCount x n + prefixCount (fun i => !(x i)) n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases hx : x n <;> simp [prefix_succ, hx] <;> omega

theorem prefix_eq_zero (x : Nat -> Bool) (n : Nat) :
    prefixCount x n = 0 <-> forall i, i < n -> x i = false := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prefix_succ, Nat.add_eq_zero_iff, ih]
    have hb : (if x n then 1 else 0) = 0 <-> x n = false := by cases x n <;> simp
    rw [hb]
    constructor
    · rintro ⟨h, hn⟩ i hi
      by_cases hin : i < n
      · exact h i hin
      · have : i = n := by omega
        simpa [this] using hn
    · intro h
      exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

/-- The transparent row encoder's negative/zero/tautological branches. -/
def rowCNF (n : Nat) (cap : Int) : CNF CounterVar :=
  if (n : Int) <= cap then .empty else
  if cap < 0 then ofClauses [[]] else
  if cap = 0 then ofClauses ((List.range n).map (fun i => [(input i, false)])) else
  atMostCNF n cap.toNat

theorem rowCNF_correct (x : Nat -> Bool) (n : Nat) (cap : Int) :
    (exists y, CNF.Sat (assign x y) (rowCNF n cap)) <->
      (prefixCount x n : Int) <= cap := by
  have hn := prefix_le x n
  by_cases ht : (n : Int) <= cap
  · simp only [rowCNF, if_pos ht, CNF.sat_empty, exists_const, true_iff]
    exact le_trans (Nat.cast_le.mpr hn) ht
  · by_cases hneg : cap < 0
    · simp [rowCNF, ht, hneg, CNF.Clause.eval]
      omega
    · by_cases hz : cap = 0
      · subst cap
        simp only [rowCNF, if_neg ht, lt_self_iff_false, ↓reduceIte, sat_ofClauses,
          List.forall_mem_map, List.mem_range]
        have he : forall y : Nat -> Nat -> Bool,
            (forall i, i < n -> CNF.Clause.eval (assign x y) [(input i,false)] = true) <->
            prefixCount x n = 0 := by
          intro y
          simp [CNF.Clause.eval, assign, input, prefix_eq_zero]
        simp only [he, exists_const]
        omega
      · simp only [rowCNF, if_neg ht, if_neg hneg, if_neg hz, atMostCNF_correct]
        have hc : (cap.toNat : Int) = cap := Int.toNat_of_nonneg (by omega)
        omega

/-- Flip the sign of primary literals; auxiliary signs are unchanged. -/
def flipPrimaryLiteral : Literal CounterVar -> Literal CounterVar
  | (.inl i, b) => (.inl i, !b)
  | (.inr ij, b) => (.inr ij, b)

def flipPrimary (f : CNF CounterVar) : CNF CounterVar :=
  ⟨f.clauses.map (fun c => c.map flipPrimaryLiteral)⟩

theorem eval_flip_clause (x : Nat -> Bool) (y : Nat -> Nat -> Bool)
    (c : CNF.Clause CounterVar) :
    CNF.Clause.eval (assign x y) (c.map flipPrimaryLiteral) =
      CNF.Clause.eval (assign (fun i => !(x i)) y) c := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    rcases l with ⟨i | ij, b⟩
    · cases b <;> cases hx : x i <;>
        simp [CNF.Clause.eval_cons, flipPrimaryLiteral, ih, assign, hx]
    · simp [CNF.Clause.eval_cons, flipPrimaryLiteral, ih, assign]

theorem sat_flipPrimary (x : Nat -> Bool) (y : Nat -> Nat -> Bool)
    (f : CNF CounterVar) :
    CNF.Sat (assign x y) (flipPrimary f) <->
      CNF.Sat (assign (fun i => !(x i)) y) f := by
  simp [CNF.Sat, CNF.eval, flipPrimary, eval_flip_clause]

def atLeastCNF (n k : Nat) : CNF CounterVar :=
  flipPrimary (rowCNF n ((n : Int) - k))

theorem atLeastCNF_correct (x : Nat -> Bool) (n k : Nat) :
    (exists y, CNF.Sat (assign x y) (atLeastCNF n k)) <-> k <= prefixCount x n := by
  simp only [atLeastCNF, sat_flipPrimary, rowCNF_correct]
  have h := prefix_complement x n
  omega

/-- Separate upper and lower counter witnesses, with no auxiliary aliasing. -/
theorem exact_two_counters (x : Nat -> Bool) (n k : Nat) :
    (exists upper lower,
      CNF.Sat (assign x upper) (rowCNF n k) ∧
      CNF.Sat (assign x lower) (atLeastCNF n k)) <-> prefixCount x n = k := by
  have he : (exists upper lower,
      CNF.Sat (assign x upper) (rowCNF n k) ∧
      CNF.Sat (assign x lower) (atLeastCNF n k)) <->
      (exists upper, CNF.Sat (assign x upper) (rowCNF n k)) ∧
      (exists lower, CNF.Sat (assign x lower) (atLeastCNF n k)) := by
    constructor
    · rintro ⟨u,l,hu,hl⟩; exact ⟨⟨u,hu⟩,⟨l,hl⟩⟩
    · rintro ⟨⟨u,hu⟩,⟨l,hl⟩⟩; exact ⟨u,l,hu,hl⟩
  rw [he, rowCNF_correct, atLeastCNF_correct]
  omega

end Qiushi.CNF
