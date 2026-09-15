
-- Auto-generated orbit 486 leaf 2
-- 41 witness rows, branch depth 4
-- Branch hypotheses hbrk match the exact path[k] inequality stored by extract_leaves.

import Mathlib
import QiushiOccupationSoundness
import QiushiOrbit486Data

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

namespace QiushiMatmul

def refs_486_L2 : Fin 41 → RowRef 169 40
  | i => match i.val with
  | 0 => .occ ⟨3, by decide⟩
  | 1 => .occ ⟨54, by decide⟩
  | 2 => .occ ⟨55, by decide⟩
  | 3 => .occ ⟨56, by decide⟩
  | 4 => .occ ⟨57, by decide⟩
  | 5 => .occ ⟨7, by decide⟩
  | 6 => .occ ⟨8, by decide⟩
  | 7 => .occ ⟨37, by decide⟩
  | 8 => .occ ⟨12, by decide⟩
  | 9 => .occ ⟨13, by decide⟩
  | 10 => .occ ⟨58, by decide⟩
  | 11 => .occ ⟨40, by decide⟩
  | 12 => .occ ⟨14, by decide⟩
  | 13 => .occ ⟨59, by decide⟩
  | 14 => .occ ⟨16, by decide⟩
  | 15 => .occ ⟨18, by decide⟩
  | 16 => .occ ⟨60, by decide⟩
  | 17 => .occ ⟨19, by decide⟩
  | 18 => .occ ⟨61, by decide⟩
  | 19 => .occ ⟨21, by decide⟩
  | 20 => .occ ⟨62, by decide⟩
  | 21 => .occ ⟨63, by decide⟩
  | 22 => .occ ⟨64, by decide⟩
  | 23 => .occ ⟨25, by decide⟩
  | 24 => .occ ⟨65, by decide⟩
  | 25 => .occ ⟨26, by decide⟩
  | 26 => .occ ⟨27, by decide⟩
  | 27 => .occ ⟨30, by decide⟩
  | 28 => .occ ⟨31, by decide⟩
  | 29 => .occ ⟨66, by decide⟩
  | 30 => .occ ⟨67, by decide⟩
  | 31 => .occ ⟨50, by decide⟩
  | 32 => .occ ⟨68, by decide⟩
  | 33 => .occ ⟨69, by decide⟩
  | 34 => .sumGe
  | 35 => .nonneg ⟨6, by decide⟩
  | 36 => .nonneg ⟨27, by decide⟩
  | 37 => .branchLe ⟨13, by decide⟩ 0
  | 38 => .branchLe ⟨36, by decide⟩ 0
  | 39 => .branchGe ⟨14, by decide⟩ 1
  | 40 => .branchLe ⟨31, by decide⟩ 0
  | _ => .sumGe

def mults_486_L2 : Fin 41 → Nat
  | i => match i.val with
  | 0 => 48098
  | 1 => 14414
  | 2 => 53882
  | 3 => 64508
  | 4 => 21522
  | 5 => 16739
  | 6 => 54404
  | 7 => 73524
  | 8 => 66600
  | 9 => 16686
  | 10 => 63762
  | 11 => 1847
  | 12 => 52088
  | 13 => 86203
  | 14 => 88438
  | 15 => 25606
  | 16 => 53914
  | 17 => 106201
  | 18 => 35639
  | 19 => 44055
  | 20 => 136442
  | 21 => 37595
  | 22 => 25696
  | 23 => 20375
  | 24 => 27132
  | 25 => 24090
  | 26 => 87852
  | 27 => 8458
  | 28 => 25792
  | 29 => 1890
  | 30 => 11247
  | 31 => 26480
  | 32 => 6675
  | 33 => 33199
  | 34 => 264947
  | 35 => 4783
  | 36 => 5870
  | 37 => 200439
  | 38 => 20298
  | 39 => 430546
  | 40 => 239341
  | _ => 0

theorem coeff_cancel_486_L2 :
    ∀ j : Fin 40, (∑ i : Fin 41, (mults_486_L2 i : Int) * (refs_486_L2 i).resolveCoeff S_486 j) = 0 := by
  decide

theorem rhs_neg_486_L2 :
    (∑ i : Fin 41, (mults_486_L2 i : Int) * (refs_486_L2 i).resolveRhs S_486) < 0 := by
  decide

theorem leaf2_infeasible_486 (x : Fin 40 → Int)
    (hroot : S_486.RootHolds x)
    (hbr0 : x ⟨13, by decide⟩ ≤ 0)
    (hbr1 : x ⟨36, by decide⟩ ≤ 0)
    (hbr2 : (1 : Int) ≤ x ⟨14, by decide⟩)
    (hbr3 : x ⟨31, by decide⟩ ≤ 0)
    : False := by
  have hrows : ∀ i : Fin 41,
      (∑ j : Fin 40, (refs_486_L2 i).resolveCoeff S_486 j * x j) ≤
      (refs_486_L2 i).resolveRhs S_486 := by
    intro i; fin_cases i
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum]; exact neg_le_neg hroot.hTotal
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [neg_one_mul]; exact neg_nonpos_of_nonneg (hroot.hNonneg _)
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [neg_one_mul]; exact neg_nonpos_of_nonneg (hroot.hNonneg _)
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [one_mul]; exact hbr0
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [one_mul]; exact hbr1
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [neg_one_mul]; exact neg_le_neg hbr2
    · simp only [refs_486_L2, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [one_mul]; exact hbr3
  exact farkas_leaf_unsat _ _ (mults_486_L2)
    coeff_cancel_486_L2 rhs_neg_486_L2
    x hrows

end QiushiMatmul
