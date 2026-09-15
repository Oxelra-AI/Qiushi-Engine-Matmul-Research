
-- Auto-generated orbit 486 leaf 7
-- 41 witness rows, branch depth 3
-- Branch hypotheses hbrk match the exact path[k] inequality stored by extract_leaves.

import Mathlib
import QiushiOccupationSoundness
import QiushiOrbit486Data

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

namespace QiushiMatmul

def refs_486_L7 : Fin 41 → RowRef 169 40
  | i => match i.val with
  | 0 => .occ ⟨125, by decide⟩
  | 1 => .occ ⟨2, by decide⟩
  | 2 => .occ ⟨3, by decide⟩
  | 3 => .occ ⟨126, by decide⟩
  | 4 => .occ ⟨71, by decide⟩
  | 5 => .occ ⟨127, by decide⟩
  | 6 => .occ ⟨128, by decide⟩
  | 7 => .occ ⟨56, by decide⟩
  | 8 => .occ ⟨7, by decide⟩
  | 9 => .occ ⟨129, by decide⟩
  | 10 => .occ ⟨8, by decide⟩
  | 11 => .occ ⟨130, by decide⟩
  | 12 => .occ ⟨11, by decide⟩
  | 13 => .occ ⟨12, by decide⟩
  | 14 => .occ ⟨13, by decide⟩
  | 15 => .occ ⟨40, by decide⟩
  | 16 => .occ ⟨15, by decide⟩
  | 17 => .occ ⟨131, by decide⟩
  | 18 => .occ ⟨16, by decide⟩
  | 19 => .occ ⟨101, by decide⟩
  | 20 => .occ ⟨18, by decide⟩
  | 21 => .occ ⟨19, by decide⟩
  | 22 => .occ ⟨21, by decide⟩
  | 23 => .occ ⟨22, by decide⟩
  | 24 => .occ ⟨62, by decide⟩
  | 25 => .occ ⟨132, by decide⟩
  | 26 => .occ ⟨133, by decide⟩
  | 27 => .occ ⟨134, by decide⟩
  | 28 => .occ ⟨135, by decide⟩
  | 29 => .occ ⟨136, by decide⟩
  | 30 => .occ ⟨137, by decide⟩
  | 31 => .occ ⟨138, by decide⟩
  | 32 => .occ ⟨26, by decide⟩
  | 33 => .occ ⟨28, by decide⟩
  | 34 => .occ ⟨50, by decide⟩
  | 35 => .occ ⟨139, by decide⟩
  | 36 => .sumGe
  | 37 => .nonneg ⟨9, by decide⟩
  | 38 => .branchGe ⟨13, by decide⟩ 1
  | 39 => .branchLe ⟨24, by decide⟩ 0
  | 40 => .branchLe ⟨19, by decide⟩ 0
  | _ => .sumGe

def mults_486_L7 : Fin 41 → Nat
  | i => match i.val with
  | 0 => 13749
  | 1 => 17768
  | 2 => 192966
  | 3 => 28480
  | 4 => 75447
  | 5 => 43490
  | 6 => 23287
  | 7 => 121312
  | 8 => 41025
  | 9 => 29413
  | 10 => 8768
  | 11 => 47181
  | 12 => 3253
  | 13 => 25617
  | 14 => 27810
  | 15 => 21965
  | 16 => 118449
  | 17 => 6347
  | 18 => 24115
  | 19 => 5671
  | 20 => 28053
  | 21 => 49716
  | 22 => 51901
  | 23 => 97824
  | 24 => 13826
  | 25 => 31039
  | 26 => 36967
  | 27 => 8253
  | 28 => 14040
  | 29 => 1624
  | 30 => 26006
  | 31 => 91627
  | 32 => 15349
  | 33 => 25536
  | 34 => 5928
  | 35 => 14897
  | 36 => 200518
  | 37 => 10579
  | 38 => 406142
  | 39 => 168150
  | 40 => 141732
  | _ => 0

theorem coeff_cancel_486_L7 :
    ∀ j : Fin 40, (∑ i : Fin 41, (mults_486_L7 i : Int) * (refs_486_L7 i).resolveCoeff S_486 j) = 0 := by
  decide

theorem rhs_neg_486_L7 :
    (∑ i : Fin 41, (mults_486_L7 i : Int) * (refs_486_L7 i).resolveRhs S_486) < 0 := by
  decide

theorem leaf7_infeasible_486 (x : Fin 40 → Int)
    (hroot : S_486.RootHolds x)
    (hbr0 : (1 : Int) ≤ x ⟨13, by decide⟩)
    (hbr1 : x ⟨24, by decide⟩ ≤ 0)
    (hbr2 : x ⟨19, by decide⟩ ≤ 0)
    : False := by
  have hrows : ∀ i : Fin 41,
      (∑ j : Fin 40, (refs_486_L7 i).resolveCoeff S_486 j * x j) ≤
      (refs_486_L7 i).resolveRhs S_486 := by
    intro i; fin_cases i
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum]; exact neg_le_neg hroot.hTotal
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [neg_one_mul]; exact neg_nonpos_of_nonneg (hroot.hNonneg _)
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [neg_one_mul]; exact neg_le_neg hbr0
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [one_mul]; exact hbr1
    · simp only [refs_486_L7, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [one_mul]; exact hbr2
  exact farkas_leaf_unsat _ _ (mults_486_L7)
    coeff_cancel_486_L7 rhs_neg_486_L7
    x hrows

end QiushiMatmul
