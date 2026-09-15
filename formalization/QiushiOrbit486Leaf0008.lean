
-- Auto-generated orbit 486 leaf 8
-- 41 witness rows, branch depth 3
-- Branch hypotheses hbrk match the exact path[k] inequality stored by extract_leaves.

import Mathlib
import QiushiOccupationSoundness
import QiushiOrbit486Data

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

namespace QiushiMatmul

def refs_486_L8 : Fin 41 → RowRef 169 40
  | i => match i.val with
  | 0 => .occ ⟨140, by decide⟩
  | 1 => .occ ⟨3, by decide⟩
  | 2 => .occ ⟨6, by decide⟩
  | 3 => .occ ⟨141, by decide⟩
  | 4 => .occ ⟨142, by decide⟩
  | 5 => .occ ⟨143, by decide⟩
  | 6 => .occ ⟨56, by decide⟩
  | 7 => .occ ⟨8, by decide⟩
  | 8 => .occ ⟨11, by decide⟩
  | 9 => .occ ⟨12, by decide⟩
  | 10 => .occ ⟨115, by decide⟩
  | 11 => .occ ⟨13, by decide⟩
  | 12 => .occ ⟨40, by decide⟩
  | 13 => .occ ⟨15, by decide⟩
  | 14 => .occ ⟨16, by decide⟩
  | 15 => .occ ⟨18, by decide⟩
  | 16 => .occ ⟨144, by decide⟩
  | 17 => .occ ⟨19, by decide⟩
  | 18 => .occ ⟨41, by decide⟩
  | 19 => .occ ⟨118, by decide⟩
  | 20 => .occ ⟨119, by decide⟩
  | 21 => .occ ⟨22, by decide⟩
  | 22 => .occ ⟨62, by decide⟩
  | 23 => .occ ⟨145, by decide⟩
  | 24 => .occ ⟨146, by decide⟩
  | 25 => .occ ⟨147, by decide⟩
  | 26 => .occ ⟨148, by decide⟩
  | 27 => .occ ⟨138, by decide⟩
  | 28 => .occ ⟨31, by decide⟩
  | 29 => .occ ⟨67, by decide⟩
  | 30 => .occ ⟨149, by decide⟩
  | 31 => .occ ⟨150, by decide⟩
  | 32 => .occ ⟨151, by decide⟩
  | 33 => .occ ⟨152, by decide⟩
  | 34 => .occ ⟨153, by decide⟩
  | 35 => .sumGe
  | 36 => .nonneg ⟨33, by decide⟩
  | 37 => .nonneg ⟨34, by decide⟩
  | 38 => .branchGe ⟨13, by decide⟩ 1
  | 39 => .branchLe ⟨24, by decide⟩ 0
  | 40 => .branchGe ⟨19, by decide⟩ 1
  | _ => .sumGe

def mults_486_L8 : Fin 41 → Nat
  | i => match i.val with
  | 0 => 1643
  | 1 => 3259
  | 2 => 7044
  | 3 => 1478
  | 4 => 150
  | 5 => 1174
  | 6 => 3162
  | 7 => 4418
  | 8 => 696
  | 9 => 1014
  | 10 => 1622
  | 11 => 298
  | 12 => 3658
  | 13 => 3991
  | 14 => 809
  | 15 => 4036
  | 16 => 2198
  | 17 => 1026
  | 18 => 1514
  | 19 => 530
  | 20 => 852
  | 21 => 3890
  | 22 => 910
  | 23 => 110
  | 24 => 864
  | 25 => 1596
  | 26 => 1112
  | 27 => 2180
  | 28 => 116
  | 29 => 931
  | 30 => 3569
  | 31 => 743
  | 32 => 197
  | 33 => 1494
  | 34 => 157
  | 35 => 9497
  | 36 => 1206
  | 37 => 728
  | 38 => 15010
  | 39 => 4922
  | 40 => 17520
  | _ => 0

theorem coeff_cancel_486_L8 :
    ∀ j : Fin 40, (∑ i : Fin 41, (mults_486_L8 i : Int) * (refs_486_L8 i).resolveCoeff S_486 j) = 0 := by
  decide

theorem rhs_neg_486_L8 :
    (∑ i : Fin 41, (mults_486_L8 i : Int) * (refs_486_L8 i).resolveRhs S_486) < 0 := by
  decide

theorem leaf8_infeasible_486 (x : Fin 40 → Int)
    (hroot : S_486.RootHolds x)
    (hbr0 : (1 : Int) ≤ x ⟨13, by decide⟩)
    (hbr1 : x ⟨24, by decide⟩ ≤ 0)
    (hbr2 : (1 : Int) ≤ x ⟨19, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 41,
      (∑ j : Fin 40, (refs_486_L8 i).resolveCoeff S_486 j * x j) ≤
      (refs_486_L8 i).resolveRhs S_486 := by
    intro i; fin_cases i
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum]; exact neg_le_neg hroot.hTotal
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [neg_one_mul]; exact neg_nonpos_of_nonneg (hroot.hNonneg _)
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [neg_one_mul]; exact neg_nonpos_of_nonneg (hroot.hNonneg _)
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [neg_one_mul]; exact neg_le_neg hbr0
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [one_mul]; exact hbr1
    · simp only [refs_486_L8, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [neg_one_mul]; exact neg_le_neg hbr2
  exact farkas_leaf_unsat _ _ (mults_486_L8)
    coeff_cancel_486_L8 rhs_neg_486_L8
    x hrows

end QiushiMatmul
