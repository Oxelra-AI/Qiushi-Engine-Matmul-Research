
-- Auto-generated orbit 486 leaf 9
-- 41 witness rows, branch depth 2
-- Branch hypotheses hbrk match the exact path[k] inequality stored by extract_leaves.

import Mathlib
import QiushiOccupationSoundness
import QiushiOrbit486Data

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

namespace QiushiMatmul

def refs_486_L9 : Fin 41 → RowRef 169 40
  | i => match i.val with
  | 0 => .occ ⟨126, by decide⟩
  | 1 => .occ ⟨154, by decide⟩
  | 2 => .occ ⟨128, by decide⟩
  | 3 => .occ ⟨155, by decide⟩
  | 4 => .occ ⟨56, by decide⟩
  | 5 => .occ ⟨7, by decide⟩
  | 6 => .occ ⟨8, by decide⟩
  | 7 => .occ ⟨114, by decide⟩
  | 8 => .occ ⟨37, by decide⟩
  | 9 => .occ ⟨156, by decide⟩
  | 10 => .occ ⟨14, by decide⟩
  | 11 => .occ ⟨15, by decide⟩
  | 12 => .occ ⟨157, by decide⟩
  | 13 => .occ ⟨158, by decide⟩
  | 14 => .occ ⟨16, by decide⟩
  | 15 => .occ ⟨18, by decide⟩
  | 16 => .occ ⟨159, by decide⟩
  | 17 => .occ ⟨144, by decide⟩
  | 18 => .occ ⟨19, by decide⟩
  | 19 => .occ ⟨20, by decide⟩
  | 20 => .occ ⟨22, by decide⟩
  | 21 => .occ ⟨160, by decide⟩
  | 22 => .occ ⟨133, by decide⟩
  | 23 => .occ ⟨25, by decide⟩
  | 24 => .occ ⟨161, by decide⟩
  | 25 => .occ ⟨162, by decide⟩
  | 26 => .occ ⟨163, by decide⟩
  | 27 => .occ ⟨164, by decide⟩
  | 28 => .occ ⟨165, by decide⟩
  | 29 => .occ ⟨166, by decide⟩
  | 30 => .occ ⟨167, by decide⟩
  | 31 => .occ ⟨138, by decide⟩
  | 32 => .occ ⟨27, by decide⟩
  | 33 => .occ ⟨67, by decide⟩
  | 34 => .occ ⟨32, by decide⟩
  | 35 => .occ ⟨168, by decide⟩
  | 36 => .sumGe
  | 37 => .nonneg ⟨30, by decide⟩
  | 38 => .nonneg ⟨37, by decide⟩
  | 39 => .branchGe ⟨13, by decide⟩ 1
  | 40 => .branchGe ⟨24, by decide⟩ 1
  | _ => .sumGe

def mults_486_L9 : Fin 41 → Nat
  | i => match i.val with
  | 0 => 66
  | 1 => 66
  | 2 => 24
  | 3 => 24
  | 4 => 215
  | 5 => 1
  | 6 => 1
  | 7 => 34
  | 8 => 236
  | 9 => 34
  | 10 => 141
  | 11 => 71
  | 12 => 229
  | 13 => 187
  | 14 => 71
  | 15 => 95
  | 16 => 131
  | 17 => 110
  | 18 => 95
  | 19 => 209
  | 20 => 188
  | 21 => 37
  | 22 => 37
  | 23 => 19
  | 24 => 28
  | 25 => 49
  | 26 => 63
  | 27 => 88
  | 28 => 88
  | 29 => 36
  | 30 => 57
  | 31 => 125
  | 32 => 125
  | 33 => 22
  | 34 => 3
  | 35 => 232
  | 36 => 575
  | 37 => 21
  | 38 => 200
  | 39 => 1191
  | 40 => 1275
  | _ => 0

theorem coeff_cancel_486_L9 :
    ∀ j : Fin 40, (∑ i : Fin 41, (mults_486_L9 i : Int) * (refs_486_L9 i).resolveCoeff S_486 j) = 0 := by
  decide

theorem rhs_neg_486_L9 :
    (∑ i : Fin 41, (mults_486_L9 i : Int) * (refs_486_L9 i).resolveRhs S_486) < 0 := by
  decide

theorem leaf9_infeasible_486 (x : Fin 40 → Int)
    (hroot : S_486.RootHolds x)
    (hbr0 : (1 : Int) ≤ x ⟨13, by decide⟩)
    (hbr1 : (1 : Int) ≤ x ⟨24, by decide⟩)
    : False := by
  have hrows : ∀ i : Fin 41,
      (∑ j : Fin 40, (refs_486_L9 i).resolveCoeff S_486 j * x j) ≤
      (refs_486_L9 i).resolveRhs S_486 := by
    intro i; fin_cases i
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs]; exact hroot.hOcc _
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs, neg_sum]; exact neg_le_neg hroot.hTotal
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [neg_one_mul]; exact neg_nonpos_of_nonneg (hroot.hNonneg _)
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [neg_one_mul]; exact neg_nonpos_of_nonneg (hroot.hNonneg _)
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [neg_one_mul]; exact neg_le_neg hbr0
    · simp only [refs_486_L9, RowRef.resolveCoeff, RowRef.resolveRhs, indicator_sum]; rw [neg_one_mul]; exact neg_le_neg hbr1
  exact farkas_leaf_unsat _ _ (mults_486_L9)
    coeff_cancel_486_L9 rhs_neg_486_L9
    x hrows

end QiushiMatmul
