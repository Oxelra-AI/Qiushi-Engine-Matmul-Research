import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0087Refs : Fin 49 → RowRef 668 48 := ![.occ 92, .occ 105, .occ 108, .occ 139, .occ 141, .occ 142, .occ 156, .occ 168, .occ 177, .occ 200, .occ 223, .occ 224, .occ 237, .occ 239, .occ 240, .occ 260, .occ 267, .occ 269, .occ 281, .occ 282, .occ 288, .occ 290, .occ 291, .occ 292, .occ 297, .occ 315, .occ 332, .occ 333, .occ 380, .occ 399, .occ 417, .occ 470, .occ 485, .occ 521, .occ 544, .occ 598, .occ 649, .occ 650, .occ 662, .occ 664, .occ 665, .sumGe, .nonneg 0, .nonneg 24, .branchGe 39 (1), .branchLe 7 (0), .branchGe 28 (1), .branchGe 3 (1), .branchGe 37 (1)]

def plane487GenLeaf0087Mult : Fin 49 → Nat := ![1465, 3591, 117, 338, 3033, 1682, 2558, 618, 714, 4610, 98, 2638, 2665, 929, 670, 4809, 1290, 760, 386, 519, 304, 183, 408, 880, 1997, 623, 2413, 90, 912, 430, 607, 777, 287, 319, 355, 1578, 970, 715, 2206, 1123, 21, 6209, 544, 175, 11041, 3493, 22345, 16928, 7226]

theorem plane487GenLeaf0087 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0087Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0087Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0087Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0087Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 92
  · exact hroot.hOcc 105
  · exact hroot.hOcc 108
  · exact hroot.hOcc 139
  · exact hroot.hOcc 141
  · exact hroot.hOcc 142
  · exact hroot.hOcc 156
  · exact hroot.hOcc 168
  · exact hroot.hOcc 177
  · exact hroot.hOcc 200
  · exact hroot.hOcc 223
  · exact hroot.hOcc 224
  · exact hroot.hOcc 237
  · exact hroot.hOcc 239
  · exact hroot.hOcc 240
  · exact hroot.hOcc 260
  · exact hroot.hOcc 267
  · exact hroot.hOcc 269
  · exact hroot.hOcc 281
  · exact hroot.hOcc 282
  · exact hroot.hOcc 288
  · exact hroot.hOcc 290
  · exact hroot.hOcc 291
  · exact hroot.hOcc 292
  · exact hroot.hOcc 297
  · exact hroot.hOcc 315
  · exact hroot.hOcc 332
  · exact hroot.hOcc 333
  · exact hroot.hOcc 380
  · exact hroot.hOcc 399
  · exact hroot.hOcc 417
  · exact hroot.hOcc 470
  · exact hroot.hOcc 485
  · exact hroot.hOcc 521
  · exact hroot.hOcc 544
  · exact hroot.hOcc 598
  · exact hroot.hOcc 649
  · exact hroot.hOcc 650
  · exact hroot.hOcc 662
  · exact hroot.hOcc 664
  · exact hroot.hOcc 665
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (24 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (7 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (28 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (3 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3
  · change (∑ k, (if k = (37 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37

end QiushiMatmul
