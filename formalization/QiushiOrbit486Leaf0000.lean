
-- Auto-generated orbit 486 leaf 0
-- 41 witness rows, branch depth 4
-- Branch hypotheses hbrk match the exact path[k] inequality stored by extract_leaves.

import Mathlib
import QiushiOccupationSoundness
import QiushiOrbit486Data

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

namespace QiushiMatmul

def refs_486_L0 : Fin 41 → RowRef 169 40
  | i => match i.val with
  | 0 => .occ ⟨0, by decide⟩
  | 1 => .occ ⟨1, by decide⟩
  | 2 => .occ ⟨2, by decide⟩
  | 3 => .occ ⟨3, by decide⟩
  | 4 => .occ ⟨4, by decide⟩
  | 5 => .occ ⟨5, by decide⟩
  | 6 => .occ ⟨6, by decide⟩
  | 7 => .occ ⟨7, by decide⟩
  | 8 => .occ ⟨8, by decide⟩
  | 9 => .occ ⟨9, by decide⟩
  | 10 => .occ ⟨10, by decide⟩
  | 11 => .occ ⟨11, by decide⟩
  | 12 => .occ ⟨12, by decide⟩
  | 13 => .occ ⟨13, by decide⟩
  | 14 => .occ ⟨14, by decide⟩
  | 15 => .occ ⟨15, by decide⟩
  | 16 => .occ ⟨16, by decide⟩
  | 17 => .occ ⟨17, by decide⟩
  | 18 => .occ ⟨18, by decide⟩
  | 19 => .occ ⟨19, by decide⟩
  | 20 => .occ ⟨20, by decide⟩
  | 21 => .occ ⟨21, by decide⟩
  | 22 => .occ ⟨22, by decide⟩
  | 23 => .occ ⟨23, by decide⟩
  | 24 => .occ ⟨24, by decide⟩
  | 25 => .occ ⟨25, by decide⟩
  | 26 => .occ ⟨26, by decide⟩
  | 27 => .occ ⟨27, by decide⟩
  | 28 => .occ ⟨28, by decide⟩
  | 29 => .occ ⟨29, by decide⟩
  | 30 => .occ ⟨30, by decide⟩
  | 31 => .occ ⟨31, by decide⟩
  | 32 => .occ ⟨32, by decide⟩
  | 33 => .occ ⟨33, by decide⟩
  | 34 => .occ ⟨34, by decide⟩
  | 35 => .sumGe
  | 36 => .nonneg ⟨7, by decide⟩
  | 37 => .branchLe ⟨13, by decide⟩ 0
  | 38 => .branchLe ⟨36, by decide⟩ 0
  | 39 => .branchLe ⟨14, by decide⟩ 0
  | 40 => .branchLe ⟨17, by decide⟩ 0
  | _ => .sumGe

def mults_486_L0 : Fin 41 → Nat
  | i => match i.val with
  | 0 => 1437
  | 1 => 605
  | 2 => 9420
  | 3 => 8233
  | 4 => 1219
  | 5 => 1002
  | 6 => 2961
  | 7 => 4164
  | 8 => 4488
  | 9 => 1736
  | 10 => 8
  | 11 => 2674
  | 12 => 3362
  | 13 => 2655
  | 14 => 2032
  | 15 => 3897
  | 16 => 2720
  | 17 => 1529
  | 18 => 6444
  | 19 => 3971
  | 20 => 3427
  | 21 => 3112
  | 22 => 1976
  | 23 => 459
  | 24 => 373
  | 25 => 2847
  | 26 => 1102
  | 27 => 287
  | 28 => 254
  | 29 => 2105
  | 30 => 1294
  | 31 => 1695
  | 32 => 115
  | 33 => 463
  | 34 => 1552
  | 35 => 13377
  | 36 => 2617
  | 37 => 5489
  | 38 => 10657
  | 39 => 9004
  | 40 => 9226
  | _ => 0

theorem coeff_cancel_486_L0 :
    ∀ j : Fin 40, (∑ i : Fin 41, (mults_486_L0 i : Int) * (refs_486_L0 i).resolveCoeff S_486 j) = 0 := by
  decide

theorem rhs_neg_486_L0 :
    (∑ i : Fin 41, (mults_486_L0 i : Int) * (refs_486_L0 i).resolveRhs S_486) < 0 := by
  decide

theorem leaf0_infeasible_486 (x : Fin 40 → Int)
    (hroot : S_486.RootHolds x)
    (hbr0 : x ⟨13, by decide⟩ ≤ 0)
    (hbr1 : x ⟨36, by decide⟩ ≤ 0)
    (hbr2 : x ⟨14, by decide⟩ ≤ 0)
    (hbr3 : x ⟨17, by decide⟩ ≤ 0)
    : False := by
  have hrows : ∀ i : Fin 41,
      (∑ j : Fin 40, (refs_486_L0 i).resolveCoeff S_486 j * x j) ≤
      (refs_486_L0 i).resolveRhs S_486 := by
    intro i; fin_cases i
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum]; exact neg_le_neg hroot.hTotal
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [neg_one_mul]; exact neg_nonpos_of_nonneg (hroot.hNonneg _)
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [one_mul]; exact hbr0
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [one_mul]; exact hbr1
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [one_mul]; exact hbr2
    · simp only [refs_486_L0, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [one_mul]; exact hbr3
  exact farkas_leaf_unsat _ _ (mults_486_L0)
    coeff_cancel_486_L0 rhs_neg_486_L0
    x hrows

end QiushiMatmul
