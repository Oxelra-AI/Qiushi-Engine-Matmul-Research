import Mathlib.Data.List.Sort

namespace QiushiMatmul.Calibration

/-- Structural fuel avoids reducing the well-founded recursion proofs in the
library sort while retaining exactly its stable order. -/
def mergeFuel {α : Type*} (le : α → α → Bool) : Nat → List α → List α → List α
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, xs, [] => xs
  | n + 1, x :: xs, y :: ys =>
    if le x y then x :: mergeFuel le n xs (y :: ys)
    else y :: mergeFuel le n (x :: xs) ys

theorem mergeFuel_eq {α : Type*} (le : α → α → Bool) (n : Nat)
    (xs ys : List α) (h : xs.length + ys.length ≤ n) :
    mergeFuel le n xs ys = xs.merge ys le := by
  induction n generalizing xs ys with
  | zero =>
    have hx : xs = [] := List.length_eq_zero_iff.mp (by omega)
    have hy : ys = [] := List.length_eq_zero_iff.mp (by omega)
    subst xs; subst ys; simp [mergeFuel]
  | succ n ih =>
    cases xs with
    | nil => simp [mergeFuel]
    | cons x xs =>
      cases ys with
      | nil => simp [mergeFuel]
      | cons y ys =>
        simp only [mergeFuel, List.merge]
        split <;> congr 1 <;> apply ih <;> simp_all only [List.length_cons] <;> omega

def sortFuel {α : Type*} (le : α → α → Bool) : Nat → List α → List α
  | 0, xs => xs
  | _ + 1, [] => []
  | _ + 1, [x] => [x]
  | n + 1, xs@(_ :: _ :: _) =>
    let k := (xs.length + 1) / 2
    let l := sortFuel le n (xs.take k)
    let r := sortFuel le n (xs.drop k)
    mergeFuel le xs.length l r

theorem sortFuel_eq {α : Type*} (le : α → α → Bool) (n : Nat)
    (xs : List α) (h : xs.length ≤ n) : sortFuel le n xs = xs.mergeSort le := by
  induction n generalizing xs with
  | zero =>
    have hx : xs = [] := List.length_eq_zero_iff.mp (by omega)
    subst xs
    simp [sortFuel]
  | succ n ih =>
    cases xs with
    | nil => simp [sortFuel]
    | cons x xs =>
      cases xs with
      | nil => simp [sortFuel]
      | cons y xs =>
        have hl := ih ((x :: y :: xs).take (((x :: y :: xs).length + 1) / 2)) (by
          simp_all only [List.length_take, List.length_cons]
          omega)
        have hr := ih ((x :: y :: xs).drop (((x :: y :: xs).length + 1) / 2)) (by
          simp_all only [List.length_drop, List.length_cons]
          omega)
        simp only [sortFuel]
        rw [hl, hr, mergeFuel_eq]
        · simp only [List.mergeSort, List.MergeSort.Internal.splitInTwo_fst,
            List.MergeSort.Internal.splitInTwo_snd]
        · simp only [List.length_mergeSort, List.length_take, List.length_drop]
          omega

end QiushiMatmul.Calibration
