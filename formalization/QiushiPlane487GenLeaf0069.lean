import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0069Refs : Fin 49 → RowRef 668 48 := ![.occ 83, .occ 94, .occ 95, .occ 101, .occ 104, .occ 106, .occ 135, .occ 145, .occ 146, .occ 154, .occ 162, .occ 190, .occ 215, .occ 224, .occ 225, .occ 227, .occ 231, .occ 236, .occ 253, .occ 281, .occ 297, .occ 303, .occ 330, .occ 331, .occ 351, .occ 399, .occ 415, .occ 481, .occ 496, .occ 498, .occ 519, .occ 528, .occ 529, .occ 560, .occ 572, .occ 645, .occ 648, .occ 664, .occ 665, .sumGe, .nonneg 7, .branchGe 39 (1), .branchLe 28 (0), .branchLe 40 (0), .branchGe 29 (1), .branchLe 10 (0), .branchLe 12 (0), .branchLe 16 (0), .branchGe 20 (1)]

def plane487GenLeaf0069Mult : Fin 49 → Nat := ![162, 24, 116, 24, 10, 64, 194, 16, 6, 5, 9, 13, 49, 7, 63, 39, 46, 6, 30, 6, 127, 52, 31, 3, 40, 127, 42, 24, 7, 30, 121, 131, 23, 42, 16, 94, 19, 36, 17, 294, 149, 157, 270, 206, 560, 180, 239, 54, 880]

theorem plane487GenLeaf0069 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0069Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0069Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0069Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0069Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 83
  · exact hroot.hOcc 94
  · exact hroot.hOcc 95
  · exact hroot.hOcc 101
  · exact hroot.hOcc 104
  · exact hroot.hOcc 106
  · exact hroot.hOcc 135
  · exact hroot.hOcc 145
  · exact hroot.hOcc 146
  · exact hroot.hOcc 154
  · exact hroot.hOcc 162
  · exact hroot.hOcc 190
  · exact hroot.hOcc 215
  · exact hroot.hOcc 224
  · exact hroot.hOcc 225
  · exact hroot.hOcc 227
  · exact hroot.hOcc 231
  · exact hroot.hOcc 236
  · exact hroot.hOcc 253
  · exact hroot.hOcc 281
  · exact hroot.hOcc 297
  · exact hroot.hOcc 303
  · exact hroot.hOcc 330
  · exact hroot.hOcc 331
  · exact hroot.hOcc 351
  · exact hroot.hOcc 399
  · exact hroot.hOcc 415
  · exact hroot.hOcc 481
  · exact hroot.hOcc 496
  · exact hroot.hOcc 498
  · exact hroot.hOcc 519
  · exact hroot.hOcc 528
  · exact hroot.hOcc 529
  · exact hroot.hOcc 560
  · exact hroot.hOcc 572
  · exact hroot.hOcc 645
  · exact hroot.hOcc 648
  · exact hroot.hOcc 664
  · exact hroot.hOcc 665
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (28 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (40 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (29 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (10 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (12 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (16 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (20 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20

end QiushiMatmul
