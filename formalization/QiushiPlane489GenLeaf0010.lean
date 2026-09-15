import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0010Refs : Fin 33 → RowRef 371 32 := ![.occ 102, .occ 110, .occ 122, .occ 129, .occ 130, .occ 154, .occ 155, .occ 158, .occ 163, .occ 167, .occ 187, .occ 197, .occ 208, .occ 281, .occ 288, .occ 303, .occ 304, .occ 306, .occ 338, .occ 341, .occ 344, .occ 345, .occ 348, .occ 356, .occ 366, .sumGe, .nonneg 25, .nonneg 30, .branchLe 14 (0), .branchLe 9 (0), .branchGe 31 (1), .branchLe 23 (0), .branchGe 4 (1)]

def plane489GenLeaf0010Mult : Fin 33 → Nat := ![203, 75, 21, 143, 1, 180, 117, 139, 75, 37, 30, 45, 248, 83, 39, 21, 30, 144, 15, 212, 45, 319, 257, 134, 67, 580, 30, 275, 344, 579, 335, 323, 1650]

theorem plane489GenLeaf0010 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0010Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0010Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0010Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0010Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 102
  · exact hroot.hOcc 110
  · exact hroot.hOcc 122
  · exact hroot.hOcc 129
  · exact hroot.hOcc 130
  · exact hroot.hOcc 154
  · exact hroot.hOcc 155
  · exact hroot.hOcc 158
  · exact hroot.hOcc 163
  · exact hroot.hOcc 167
  · exact hroot.hOcc 187
  · exact hroot.hOcc 197
  · exact hroot.hOcc 208
  · exact hroot.hOcc 281
  · exact hroot.hOcc 288
  · exact hroot.hOcc 303
  · exact hroot.hOcc 304
  · exact hroot.hOcc 306
  · exact hroot.hOcc 338
  · exact hroot.hOcc 341
  · exact hroot.hOcc 344
  · exact hroot.hOcc 345
  · exact hroot.hOcc 348
  · exact hroot.hOcc 356
  · exact hroot.hOcc 366
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (25 : Fin 32) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (30 : Fin 32) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (14 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (9 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (31 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (23 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (4 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
