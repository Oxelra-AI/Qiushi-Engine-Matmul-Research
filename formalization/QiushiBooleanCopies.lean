import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
Bounded nonnegative integer occupations and unrestricted Boolean copies.
Theorems quantify over arbitrary caps and arbitrary count-dependent constraints;
they do not assert anything about the frozen DIMACS or DRAT artifacts.
-/

namespace Qiushi.CNF
open BigOperators

def bit (b : Bool) : Nat := if b then 1 else 0

@[simp] theorem bit_false : bit false = 0 := rfl
@[simp] theorem bit_true : bit true = 1 := rfl
theorem bit_le_one (b : Bool) : bit b <= 1 := by cases b <;> decide

abbrev Copies {Q : Type*} (cap : Q -> Nat) := (q : Q) -> Fin (cap q) -> Bool

def copyCount {Q : Type*} {cap : Q -> Nat} (y : Copies cap) (q : Q) : Nat :=
  ∑ j, bit (y q j)

theorem copyCount_le {Q : Type*} {cap : Q -> Nat} (y : Copies cap) (q : Q) :
    copyCount y q <= cap q := by
  calc
    _ <= ∑ _j : Fin (cap q), 1 := Finset.sum_le_sum (fun j _ => bit_le_one (y q j))
    _ = cap q := by simp

def thresholdCopies {Q : Type*} (cap x : Q -> Nat) : Copies cap :=
  fun q j => decide (j.val < x q)

theorem threshold_sum (n x : Nat) :
    (∑ j : Fin n, bit (decide (j.val < x))) = min n x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih]
    by_cases h : n < x
    · simp [bit, h]
      omega
    · simp [bit, h]
      omega

theorem copyCount_threshold {Q : Type*} (cap x : Q -> Nat)
    (h : forall q, x q <= cap q) : copyCount (thresholdCopies cap x) = x := by
  funext q
  exact (threshold_sum (cap q) (x q)).trans (Nat.min_eq_right (h q))

theorem bounded_iff_copies {Q : Type*} (cap x : Q -> Nat) :
    (forall q, x q <= cap q) <-> exists y : Copies cap, copyCount y = x := by
  constructor
  · intro h
    exact ⟨thresholdCopies cap x, copyCount_threshold cap x h⟩
  · rintro ⟨y, rfl⟩
    exact copyCount_le y

theorem bounded_integer_iff_copies {Q : Type*} (cap : Q -> Nat) (x : Q -> Int) :
    (forall q, 0 <= x q ∧ x q <= (cap q : Int)) <->
      exists y : Copies cap, forall q, (copyCount y q : Int) = x q := by
  constructor
  · intro h
    have hc : forall q, (x q).toNat <= cap q := by
      intro q
      exact Int.toNat_le.mpr (h q).2
    refine ⟨thresholdCopies cap (fun q => (x q).toNat), ?_⟩
    intro q
    rw [copyCount_threshold cap _ hc]
    exact Int.toNat_of_nonneg (h q).1
  · rintro ⟨y, hy⟩ q
    rw [← hy q]
    exact ⟨Nat.cast_nonneg _, Nat.cast_le.mpr (copyCount_le y q)⟩

/-- Every predicate depending only on the counts transfers in both directions. -/
theorem bounded_system_iff_copies {Q : Type*} (cap : Q -> Nat)
    (P : (Q -> Nat) -> Prop) :
    (exists x, (forall q, x q <= cap q) ∧ P x) <->
      exists y : Copies cap, P (copyCount y) := by
  constructor
  · rintro ⟨x, hx, hp⟩
    rcases (bounded_iff_copies cap x).mp hx with ⟨y, rfl⟩
    exact ⟨y, hp⟩
  · rintro ⟨y, hp⟩
    exact ⟨copyCount y, copyCount_le y, hp⟩

/-- The actual 0/1 row expansion, including all copies of each selected direction. -/
theorem row_sum_copies {Q : Type*} [DecidableEq Q] {cap : Q -> Nat}
    (row : Finset Q) (y : Copies cap) :
    (∑ q ∈ row, copyCount y q) =
      ∑ p ∈ row.sigma (fun _q => Finset.univ : (q : Q) -> Finset (Fin (cap q))),
        bit (y p.1 p.2) := by
  rw [Finset.sum_sigma]
  rfl

def Occupation {Q R : Type*} [Fintype Q] (rows : R -> Finset Q)
    (rhs : R -> Int) (target : Nat) (x : Q -> Nat) : Prop :=
  (∑ q, x q) = target ∧ forall r, (∑ q ∈ rows r, (x q : Int)) <= rhs r

theorem occupation_iff_copies {Q R : Type*} [Fintype Q]
    (cap : Q -> Nat) (rows : R -> Finset Q) (rhs : R -> Int) (target : Nat) :
    (exists x, (forall q, x q <= cap q) ∧ Occupation rows rhs target x) <->
      exists y : Copies cap, Occupation rows rhs target (copyCount y) :=
  bounded_system_iff_copies cap _

/-- Unary threshold monotonicity is available for the witness, not required of copies. -/
theorem threshold_monotone {Q : Type*} (cap x : Q -> Nat) (q : Q)
    (i j : Fin (cap q)) (hij : i <= j) :
    thresholdCopies cap x q j = true -> thresholdCopies cap x q i = true := by
  simp only [thresholdCopies, decide_eq_true_eq]
  exact fun h => lt_of_le_of_lt hij h

end Qiushi.CNF
