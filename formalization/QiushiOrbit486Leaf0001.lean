
-- Auto-generated orbit 486 leaf 1
-- 41 witness rows, branch depth 4
-- Branch hypotheses hbrk match the exact path[k] inequality stored by extract_leaves.

import Mathlib
import QiushiOccupationSoundness
import QiushiOrbit486Data

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

namespace QiushiMatmul

def refs_486_L1 : Fin 41 → RowRef 169 40
  | i => match i.val with
  | 0 => .occ ⟨2, by decide⟩
  | 1 => .occ ⟨3, by decide⟩
  | 2 => .occ ⟨35, by decide⟩
  | 3 => .occ ⟨7, by decide⟩
  | 4 => .occ ⟨36, by decide⟩
  | 5 => .occ ⟨8, by decide⟩
  | 6 => .occ ⟨37, by decide⟩
  | 7 => .occ ⟨9, by decide⟩
  | 8 => .occ ⟨38, by decide⟩
  | 9 => .occ ⟨11, by decide⟩
  | 10 => .occ ⟨12, by decide⟩
  | 11 => .occ ⟨39, by decide⟩
  | 12 => .occ ⟨13, by decide⟩
  | 13 => .occ ⟨40, by decide⟩
  | 14 => .occ ⟨15, by decide⟩
  | 15 => .occ ⟨16, by decide⟩
  | 16 => .occ ⟨18, by decide⟩
  | 17 => .occ ⟨19, by decide⟩
  | 18 => .occ ⟨41, by decide⟩
  | 19 => .occ ⟨42, by decide⟩
  | 20 => .occ ⟨43, by decide⟩
  | 21 => .occ ⟨44, by decide⟩
  | 22 => .occ ⟨45, by decide⟩
  | 23 => .occ ⟨20, by decide⟩
  | 24 => .occ ⟨21, by decide⟩
  | 25 => .occ ⟨25, by decide⟩
  | 26 => .occ ⟨46, by decide⟩
  | 27 => .occ ⟨47, by decide⟩
  | 28 => .occ ⟨48, by decide⟩
  | 29 => .occ ⟨49, by decide⟩
  | 30 => .occ ⟨50, by decide⟩
  | 31 => .occ ⟨51, by decide⟩
  | 32 => .occ ⟨52, by decide⟩
  | 33 => .occ ⟨53, by decide⟩
  | 34 => .sumGe
  | 35 => .nonneg ⟨37, by decide⟩
  | 36 => .nonneg ⟨38, by decide⟩
  | 37 => .branchLe ⟨13, by decide⟩ 0
  | 38 => .branchLe ⟨36, by decide⟩ 0
  | 39 => .branchLe ⟨14, by decide⟩ 0
  | 40 => .branchGe ⟨17, by decide⟩ 1
  | _ => .sumGe

def mults_486_L1 : Fin 41 → Nat
  | i => match i.val with
  | 0 => 802
  | 1 => 340
  | 2 => 446
  | 3 => 216
  | 4 => 98
  | 5 => 281
  | 6 => 818
  | 7 => 106
  | 8 => 8
  | 9 => 306
  | 10 => 310
  | 11 => 526
  | 12 => 174
  | 13 => 294
  | 14 => 598
  | 15 => 419
  | 16 => 273
  | 17 => 287
  | 18 => 137
  | 19 => 357
  | 20 => 237
  | 21 => 292
  | 22 => 4
  | 23 => 250
  | 24 => 4
  | 25 => 719
  | 26 => 278
  | 27 => 482
  | 28 => 256
  | 29 => 98
  | 30 => 482
  | 31 => 33
  | 32 => 130
  | 33 => 99
  | 34 => 1618
  | 35 => 118
  | 36 => 143
  | 37 => 857
  | 38 => 905
  | 39 => 1331
  | 40 => 3124
  | _ => 0

theorem coeff_cancel_486_L1 :
    ∀ j : Fin 40, (∑ i : Fin 41, (mults_486_L1 i : Int) * (refs_486_L1 i).resolveCoeff S_486 j) = 0 := by
  decide

theorem rhs_neg_486_L1 :
    (∑ i : Fin 41, (mults_486_L1 i : Int) * (refs_486_L1 i).resolveRhs S_486) < 0 := by
  decide

theorem leaf1_infeasible_486 (x : Fin 40 → Int)
    (hroot : S_486.RootHolds x)
    (hbr0 : x ⟨13, by decide⟩ ≤ 0)
    (hbr1 : x ⟨36, by decide⟩ ≤ 0)
    (hbr2 : x ⟨14, by decide⟩ ≤ 0)
    (hbr3 : (1 : Int) ≤ x ⟨17, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 41,
      (∑ j : Fin 40, (refs_486_L1 i).resolveCoeff S_486 j * x j) ≤
      (refs_486_L1 i).resolveRhs S_486 := by
    intro i; fin_cases i
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum]; exact neg_le_neg hroot.hTotal
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [neg_one_mul]; exact neg_nonpos_of_nonneg (hroot.hNonneg _)
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [neg_one_mul]; exact neg_nonpos_of_nonneg (hroot.hNonneg _)
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [one_mul]; exact hbr0
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [one_mul]; exact hbr1
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [one_mul]; exact hbr2
    · simp only [refs_486_L1, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [neg_one_mul]; exact neg_le_neg hbr3
  exact farkas_leaf_unsat _ _ (mults_486_L1)
    coeff_cancel_486_L1 rhs_neg_486_L1
    x hrows

end QiushiMatmul
