
-- Auto-generated orbit 486 leaf 4
-- 41 witness rows, branch depth 4
-- Branch hypotheses hbrk match the exact path[k] inequality stored by extract_leaves.

import Mathlib
import QiushiOccupationSoundness
import QiushiOrbit486Data

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

namespace QiushiMatmul

def refs_486_L4 : Fin 41 → RowRef 169 40
  | i => match i.val with
  | 0 => .occ ⟨2, by decide⟩
  | 1 => .occ ⟨86, by decide⟩
  | 2 => .occ ⟨87, by decide⟩
  | 3 => .occ ⟨35, by decide⟩
  | 4 => .occ ⟨88, by decide⟩
  | 5 => .occ ⟨7, by decide⟩
  | 6 => .occ ⟨8, by decide⟩
  | 7 => .occ ⟨37, by decide⟩
  | 8 => .occ ⟨9, by decide⟩
  | 9 => .occ ⟨12, by decide⟩
  | 10 => .occ ⟨13, by decide⟩
  | 11 => .occ ⟨89, by decide⟩
  | 12 => .occ ⟨90, by decide⟩
  | 13 => .occ ⟨40, by decide⟩
  | 14 => .occ ⟨16, by decide⟩
  | 15 => .occ ⟨18, by decide⟩
  | 16 => .occ ⟨19, by decide⟩
  | 17 => .occ ⟨91, by decide⟩
  | 18 => .occ ⟨92, by decide⟩
  | 19 => .occ ⟨42, by decide⟩
  | 20 => .occ ⟨20, by decide⟩
  | 21 => .occ ⟨22, by decide⟩
  | 22 => .occ ⟨62, by decide⟩
  | 23 => .occ ⟨23, by decide⟩
  | 24 => .occ ⟨25, by decide⟩
  | 25 => .occ ⟨93, by decide⟩
  | 26 => .occ ⟨94, by decide⟩
  | 27 => .occ ⟨95, by decide⟩
  | 28 => .occ ⟨96, by decide⟩
  | 29 => .occ ⟨66, by decide⟩
  | 30 => .occ ⟨67, by decide⟩
  | 31 => .occ ⟨97, by decide⟩
  | 32 => .occ ⟨98, by decide⟩
  | 33 => .sumGe
  | 34 => .nonneg ⟨7, by decide⟩
  | 35 => .nonneg ⟨14, by decide⟩
  | 36 => .nonneg ⟨27, by decide⟩
  | 37 => .branchLe ⟨13, by decide⟩ 0
  | 38 => .branchGe ⟨36, by decide⟩ 1
  | 39 => .branchLe ⟨19, by decide⟩ 0
  | 40 => .branchLe ⟨29, by decide⟩ 0
  | _ => .sumGe

def mults_486_L4 : Fin 41 → Nat
  | i => match i.val with
  | 0 => 100382
  | 1 => 40001
  | 2 => 6211
  | 3 => 65046
  | 4 => 16904
  | 5 => 17110
  | 6 => 15948
  | 7 => 10610
  | 8 => 22240
  | 9 => 34366
  | 10 => 7757
  | 11 => 36363
  | 12 => 12250
  | 13 => 50992
  | 14 => 80542
  | 15 => 19402
  | 16 => 34848
  | 17 => 680
  | 18 => 28530
  | 19 => 8820
  | 20 => 22370
  | 21 => 5919
  | 22 => 68415
  | 23 => 11307
  | 24 => 5511
  | 25 => 6362
  | 26 => 24551
  | 27 => 1356
  | 28 => 33044
  | 29 => 14570
  | 30 => 5500
  | 31 => 15956
  | 32 => 20407
  | 33 => 129478
  | 34 => 13113
  | 35 => 4311
  | 36 => 12499
  | 37 => 89159
  | 38 => 225584
  | 39 => 22729
  | 40 => 97209
  | _ => 0

theorem coeff_cancel_486_L4 :
    ∀ j : Fin 40, (∑ i : Fin 41, (mults_486_L4 i : Int) * (refs_486_L4 i).resolveCoeff S_486 j) = 0 := by
  decide

theorem rhs_neg_486_L4 :
    (∑ i : Fin 41, (mults_486_L4 i : Int) * (refs_486_L4 i).resolveRhs S_486) < 0 := by
  decide

theorem leaf4_infeasible_486 (x : Fin 40 → Int)
    (hroot : S_486.RootHolds x)
    (hbr0 : x ⟨13, by decide⟩ ≤ 0)
    (hbr1 : (1 : Int) ≤ x ⟨36, by decide⟩)
    (hbr2 : x ⟨19, by decide⟩ ≤ 0)
    (hbr3 : x ⟨29, by decide⟩ ≤ 0)
    : False := by
  have hrows : ∀ i : Fin 41,
      (∑ j : Fin 40, (refs_486_L4 i).resolveCoeff S_486 j * x j) ≤
      (refs_486_L4 i).resolveRhs S_486 := by
    intro i; fin_cases i
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum]; exact neg_le_neg hroot.hTotal
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [neg_one_mul]; exact neg_nonpos_of_nonneg (hroot.hNonneg _)
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [neg_one_mul]; exact neg_nonpos_of_nonneg (hroot.hNonneg _)
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [neg_one_mul]; exact neg_nonpos_of_nonneg (hroot.hNonneg _)
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [one_mul]; exact hbr0
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [neg_one_mul]; exact neg_le_neg hbr1
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [one_mul]; exact hbr2
    · simp only [refs_486_L4, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [one_mul]; exact hbr3
  exact farkas_leaf_unsat _ _ (mults_486_L4)
    coeff_cancel_486_L4 rhs_neg_486_L4
    x hrows

end QiushiMatmul
