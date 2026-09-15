
-- Auto-generated orbit 486 leaf 5
-- 41 witness rows, branch depth 4
-- Branch hypotheses hbrk match the exact path[k] inequality stored by extract_leaves.

import Mathlib
import QiushiOccupationSoundness
import QiushiOrbit486Data

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

namespace QiushiMatmul

def refs_486_L5 : Fin 41 → RowRef 169 40
  | i => match i.val with
  | 0 => .occ ⟨0, by decide⟩
  | 1 => .occ ⟨2, by decide⟩
  | 2 => .occ ⟨3, by decide⟩
  | 3 => .occ ⟨9, by decide⟩
  | 4 => .occ ⟨11, by decide⟩
  | 5 => .occ ⟨12, by decide⟩
  | 6 => .occ ⟨13, by decide⟩
  | 7 => .occ ⟨40, by decide⟩
  | 8 => .occ ⟨99, by decide⟩
  | 9 => .occ ⟨15, by decide⟩
  | 10 => .occ ⟨16, by decide⟩
  | 11 => .occ ⟨100, by decide⟩
  | 12 => .occ ⟨101, by decide⟩
  | 13 => .occ ⟨18, by decide⟩
  | 14 => .occ ⟨19, by decide⟩
  | 15 => .occ ⟨91, by decide⟩
  | 16 => .occ ⟨102, by decide⟩
  | 17 => .occ ⟨20, by decide⟩
  | 18 => .occ ⟨21, by decide⟩
  | 19 => .occ ⟨22, by decide⟩
  | 20 => .occ ⟨62, by decide⟩
  | 21 => .occ ⟨103, by decide⟩
  | 22 => .occ ⟨104, by decide⟩
  | 23 => .occ ⟨105, by decide⟩
  | 24 => .occ ⟨106, by decide⟩
  | 25 => .occ ⟨107, by decide⟩
  | 26 => .occ ⟨30, by decide⟩
  | 27 => .occ ⟨96, by decide⟩
  | 28 => .occ ⟨66, by decide⟩
  | 29 => .occ ⟨67, by decide⟩
  | 30 => .occ ⟨108, by decide⟩
  | 31 => .occ ⟨109, by decide⟩
  | 32 => .occ ⟨110, by decide⟩
  | 33 => .occ ⟨111, by decide⟩
  | 34 => .occ ⟨112, by decide⟩
  | 35 => .occ ⟨113, by decide⟩
  | 36 => .sumGe
  | 37 => .branchLe ⟨13, by decide⟩ 0
  | 38 => .branchGe ⟨36, by decide⟩ 1
  | 39 => .branchLe ⟨19, by decide⟩ 0
  | 40 => .branchGe ⟨29, by decide⟩ 1
  | _ => .sumGe

def mults_486_L5 : Fin 41 → Nat
  | i => match i.val with
  | 0 => 3808
  | 1 => 6144
  | 2 => 8192
  | 3 => 12500
  | 4 => 23979
  | 5 => 5621
  | 6 => 7583
  | 7 => 11609
  | 8 => 392
  | 9 => 8163
  | 10 => 5501
  | 11 => 16922
  | 12 => 13310
  | 13 => 11885
  | 14 => 13391
  | 15 => 3540
  | 16 => 3924
  | 17 => 2905
  | 18 => 13723
  | 19 => 4835
  | 20 => 10253
  | 21 => 12634
  | 22 => 2209
  | 23 => 3367
  | 24 => 8404
  | 25 => 5708
  | 26 => 13240
  | 27 => 5810
  | 28 => 3050
  | 29 => 7406
  | 30 => 454
  | 31 => 3054
  | 32 => 90
  | 33 => 2964
  | 34 => 13694
  | 35 => 3418
  | 36 => 51846
  | 37 => 19254
  | 38 => 60542
  | 39 => 28352
  | 40 => 97072
  | _ => 0

theorem coeff_cancel_486_L5 :
    ∀ j : Fin 40, (∑ i : Fin 41, (mults_486_L5 i : Int) * (refs_486_L5 i).resolveCoeff S_486 j) = 0 := by
  decide

theorem rhs_neg_486_L5 :
    (∑ i : Fin 41, (mults_486_L5 i : Int) * (refs_486_L5 i).resolveRhs S_486) < 0 := by
  decide

theorem leaf5_infeasible_486 (x : Fin 40 → Int)
    (hroot : S_486.RootHolds x)
    (hbr0 : x ⟨13, by decide⟩ ≤ 0)
    (hbr1 : (1 : Int) ≤ x ⟨36, by decide⟩)
    (hbr2 : x ⟨19, by decide⟩ ≤ 0)
    (hbr3 : (1 : Int) ≤ x ⟨29, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 41,
      (∑ j : Fin 40, (refs_486_L5 i).resolveCoeff S_486 j * x j) ≤
      (refs_486_L5 i).resolveRhs S_486 := by
    intro i; fin_cases i
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum]; exact neg_le_neg hroot.hTotal
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [one_mul]; exact hbr0
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [neg_one_mul]; exact neg_le_neg hbr1
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [one_mul]; exact hbr2
    · simp only [refs_486_L5, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [neg_one_mul]; exact neg_le_neg hbr3
  exact farkas_leaf_unsat _ _ (mults_486_L5)
    coeff_cancel_486_L5 rhs_neg_486_L5
    x hrows

end QiushiMatmul
