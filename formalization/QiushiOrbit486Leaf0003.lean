
-- Auto-generated orbit 486 leaf 3
-- 41 witness rows, branch depth 4
-- Branch hypotheses hbrk match the exact path[k] inequality stored by extract_leaves.

import Mathlib
import QiushiOccupationSoundness
import QiushiOrbit486Data

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

namespace QiushiMatmul

def refs_486_L3 : Fin 41 → RowRef 169 40
  | i => match i.val with
  | 0 => .occ ⟨2, by decide⟩
  | 1 => .occ ⟨3, by decide⟩
  | 2 => .occ ⟨70, by decide⟩
  | 3 => .occ ⟨71, by decide⟩
  | 4 => .occ ⟨72, by decide⟩
  | 5 => .occ ⟨55, by decide⟩
  | 6 => .occ ⟨7, by decide⟩
  | 7 => .occ ⟨73, by decide⟩
  | 8 => .occ ⟨74, by decide⟩
  | 9 => .occ ⟨11, by decide⟩
  | 10 => .occ ⟨12, by decide⟩
  | 11 => .occ ⟨13, by decide⟩
  | 12 => .occ ⟨75, by decide⟩
  | 13 => .occ ⟨16, by decide⟩
  | 14 => .occ ⟨76, by decide⟩
  | 15 => .occ ⟨18, by decide⟩
  | 16 => .occ ⟨19, by decide⟩
  | 17 => .occ ⟨77, by decide⟩
  | 18 => .occ ⟨20, by decide⟩
  | 19 => .occ ⟨21, by decide⟩
  | 20 => .occ ⟨78, by decide⟩
  | 21 => .occ ⟨64, by decide⟩
  | 22 => .occ ⟨79, by decide⟩
  | 23 => .occ ⟨80, by decide⟩
  | 24 => .occ ⟨81, by decide⟩
  | 25 => .occ ⟨82, by decide⟩
  | 26 => .occ ⟨27, by decide⟩
  | 27 => .occ ⟨28, by decide⟩
  | 28 => .occ ⟨83, by decide⟩
  | 29 => .occ ⟨66, by decide⟩
  | 30 => .occ ⟨32, by decide⟩
  | 31 => .occ ⟨84, by decide⟩
  | 32 => .occ ⟨85, by decide⟩
  | 33 => .occ ⟨53, by decide⟩
  | 34 => .sumGe
  | 35 => .nonneg ⟨10, by decide⟩
  | 36 => .nonneg ⟨38, by decide⟩
  | 37 => .branchLe ⟨13, by decide⟩ 0
  | 38 => .branchLe ⟨36, by decide⟩ 0
  | 39 => .branchGe ⟨14, by decide⟩ 1
  | 40 => .branchGe ⟨31, by decide⟩ 1
  | _ => .sumGe

def mults_486_L3 : Fin 41 → Nat
  | i => match i.val with
  | 0 => 4822
  | 1 => 8541
  | 2 => 7438
  | 3 => 9309
  | 4 => 5745
  | 5 => 173
  | 6 => 5222
  | 7 => 542
  | 8 => 4878
  | 9 => 9338
  | 10 => 939
  | 11 => 3561
  | 12 => 133
  | 13 => 567
  | 14 => 4969
  | 15 => 3438
  | 16 => 5018
  | 17 => 2505
  | 18 => 9061
  | 19 => 4103
  | 20 => 1851
  | 21 => 1847
  | 22 => 16
  | 23 => 7372
  | 24 => 7
  | 25 => 517
  | 26 => 939
  | 27 => 3679
  | 28 => 3666
  | 29 => 4484
  | 30 => 4596
  | 31 => 4076
  | 32 => 1155
  | 33 => 1990
  | 34 => 19611
  | 35 => 11672
  | 36 => 2762
  | 37 => 12239
  | 38 => 14968
  | 39 => 29180
  | 40 => 46209
  | _ => 0

theorem coeff_cancel_486_L3 :
    ∀ j : Fin 40, (∑ i : Fin 41, (mults_486_L3 i : Int) * (refs_486_L3 i).resolveCoeff S_486 j) = 0 := by
  decide

theorem rhs_neg_486_L3 :
    (∑ i : Fin 41, (mults_486_L3 i : Int) * (refs_486_L3 i).resolveRhs S_486) < 0 := by
  decide

theorem leaf3_infeasible_486 (x : Fin 40 → Int)
    (hroot : S_486.RootHolds x)
    (hbr0 : x ⟨13, by decide⟩ ≤ 0)
    (hbr1 : x ⟨36, by decide⟩ ≤ 0)
    (hbr2 : (1 : Int) ≤ x ⟨14, by decide⟩)
    (hbr3 : (1 : Int) ≤ x ⟨31, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 41,
      (∑ j : Fin 40, (refs_486_L3 i).resolveCoeff S_486 j * x j) ≤
      (refs_486_L3 i).resolveRhs S_486 := by
    intro i; fin_cases i
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum]; exact neg_le_neg hroot.hTotal
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [neg_one_mul]; exact neg_nonpos_of_nonneg (hroot.hNonneg _)
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [neg_one_mul]; exact neg_nonpos_of_nonneg (hroot.hNonneg _)
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [one_mul]; exact hbr0
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [one_mul]; exact hbr1
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [neg_one_mul]; exact neg_le_neg hbr2
    · simp only [refs_486_L3, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [neg_one_mul]; exact neg_le_neg hbr3
  exact farkas_leaf_unsat _ _ (mults_486_L3)
    coeff_cancel_486_L3 rhs_neg_486_L3
    x hrows

end QiushiMatmul
