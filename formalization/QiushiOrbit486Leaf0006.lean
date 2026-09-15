
-- Auto-generated orbit 486 leaf 6
-- 41 witness rows, branch depth 3
-- Branch hypotheses hbrk match the exact path[k] inequality stored by extract_leaves.

import Mathlib
import QiushiOccupationSoundness
import QiushiOrbit486Data

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

namespace QiushiMatmul

def refs_486_L6 : Fin 41 → RowRef 169 40
  | i => match i.val with
  | 0 => .occ ⟨2, by decide⟩
  | 1 => .occ ⟨4, by decide⟩
  | 2 => .occ ⟨35, by decide⟩
  | 3 => .occ ⟨7, by decide⟩
  | 4 => .occ ⟨8, by decide⟩
  | 5 => .occ ⟨114, by decide⟩
  | 6 => .occ ⟨37, by decide⟩
  | 7 => .occ ⟨9, by decide⟩
  | 8 => .occ ⟨12, by decide⟩
  | 9 => .occ ⟨115, by decide⟩
  | 10 => .occ ⟨89, by decide⟩
  | 11 => .occ ⟨40, by decide⟩
  | 12 => .occ ⟨116, by decide⟩
  | 13 => .occ ⟨16, by decide⟩
  | 14 => .occ ⟨117, by decide⟩
  | 15 => .occ ⟨18, by decide⟩
  | 16 => .occ ⟨19, by decide⟩
  | 17 => .occ ⟨91, by decide⟩
  | 18 => .occ ⟨118, by decide⟩
  | 19 => .occ ⟨119, by decide⟩
  | 20 => .occ ⟨20, by decide⟩
  | 21 => .occ ⟨21, by decide⟩
  | 22 => .occ ⟨62, by decide⟩
  | 23 => .occ ⟨25, by decide⟩
  | 24 => .occ ⟨106, by decide⟩
  | 25 => .occ ⟨120, by decide⟩
  | 26 => .occ ⟨121, by decide⟩
  | 27 => .occ ⟨49, by decide⟩
  | 28 => .occ ⟨31, by decide⟩
  | 29 => .occ ⟨122, by decide⟩
  | 30 => .occ ⟨96, by decide⟩
  | 31 => .occ ⟨66, by decide⟩
  | 32 => .occ ⟨67, by decide⟩
  | 33 => .occ ⟨123, by decide⟩
  | 34 => .occ ⟨124, by decide⟩
  | 35 => .sumGe
  | 36 => .nonneg ⟨7, by decide⟩
  | 37 => .nonneg ⟨15, by decide⟩
  | 38 => .branchLe ⟨13, by decide⟩ 0
  | 39 => .branchGe ⟨36, by decide⟩ 1
  | 40 => .branchGe ⟨19, by decide⟩ 1
  | _ => .sumGe

def mults_486_L6 : Fin 41 → Nat
  | i => match i.val with
  | 0 => 550
  | 1 => 5
  | 2 => 233
  | 3 => 150
  | 4 => 303
  | 5 => 280
  | 6 => 83
  | 7 => 166
  | 8 => 207
  | 9 => 48
  | 10 => 48
  | 11 => 1070
  | 12 => 476
  | 13 => 664
  | 14 => 367
  | 15 => 756
  | 16 => 255
  | 17 => 188
  | 18 => 49
  | 19 => 31
  | 20 => 79
  | 21 => 148
  | 22 => 633
  | 23 => 126
  | 24 => 2
  | 25 => 123
  | 26 => 43
  | 27 => 60
  | 28 => 283
  | 29 => 139
  | 30 => 374
  | 31 => 110
  | 32 => 168
  | 33 => 55
  | 34 => 116
  | 35 => 1325
  | 36 => 599
  | 37 => 385
  | 38 => 763
  | 39 => 2762
  | 40 => 2783
  | _ => 0

theorem coeff_cancel_486_L6 :
    ∀ j : Fin 40, (∑ i : Fin 41, (mults_486_L6 i : Int) * (refs_486_L6 i).resolveCoeff S_486 j) = 0 := by
  decide

theorem rhs_neg_486_L6 :
    (∑ i : Fin 41, (mults_486_L6 i : Int) * (refs_486_L6 i).resolveRhs S_486) < 0 := by
  decide

theorem leaf6_infeasible_486 (x : Fin 40 → Int)
    (hroot : S_486.RootHolds x)
    (hbr0 : x ⟨13, by decide⟩ ≤ 0)
    (hbr1 : (1 : Int) ≤ x ⟨36, by decide⟩)
    (hbr2 : (1 : Int) ≤ x ⟨19, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 41,
      (∑ j : Fin 40, (refs_486_L6 i).resolveCoeff S_486 j * x j) ≤
      (refs_486_L6 i).resolveRhs S_486 := by
    intro i; fin_cases i
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum]; exact neg_le_neg hroot.hTotal
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [neg_one_mul]; exact neg_nonpos_of_nonneg (hroot.hNonneg _)
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [neg_one_mul]; exact neg_nonpos_of_nonneg (hroot.hNonneg _)
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [one_mul]; exact hbr0
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [neg_one_mul]; exact neg_le_neg hbr1
    · simp only [refs_486_L6, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [neg_one_mul]; exact neg_le_neg hbr2
  exact farkas_leaf_unsat _ _ (mults_486_L6)
    coeff_cancel_486_L6 rhs_neg_486_L6
    x hrows

end QiushiMatmul
