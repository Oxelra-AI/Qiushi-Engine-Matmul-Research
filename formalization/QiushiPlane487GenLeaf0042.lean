import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0042Refs : Fin 49 → RowRef 668 48 := ![.occ 133, .occ 137, .occ 139, .occ 185, .occ 195, .occ 237, .occ 253, .occ 257, .occ 269, .occ 275, .occ 280, .occ 303, .occ 304, .occ 315, .occ 322, .occ 327, .occ 335, .occ 377, .occ 379, .occ 381, .occ 390, .occ 394, .occ 395, .occ 399, .occ 410, .occ 411, .occ 415, .occ 416, .occ 438, .occ 460, .occ 471, .occ 526, .occ 539, .occ 574, .occ 585, .occ 623, .occ 660, .occ 666, .sumGe, .nonneg 0, .nonneg 7, .nonneg 19, .nonneg 28, .nonneg 29, .branchLe 39 (0), .branchGe 23 (1), .branchLe 2 (0), .branchGe 4 (1), .branchGe 10 (1)]

def plane487GenLeaf0042Mult : Fin 49 → Nat := ![32, 1403, 1447, 392, 482, 1541, 282, 79, 3, 647, 1301, 117, 642, 1407, 11, 962, 76, 17, 167, 359, 31, 377, 396, 288, 56, 680, 141, 108, 115, 845, 165, 86, 772, 385, 120, 168, 287, 140, 2116, 670, 50, 564, 232, 120, 2030, 11653, 535, 2894, 4756]

theorem plane487GenLeaf0042 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0042Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0042Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0042Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0042Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 133
  · exact hroot.hOcc 137
  · exact hroot.hOcc 139
  · exact hroot.hOcc 185
  · exact hroot.hOcc 195
  · exact hroot.hOcc 237
  · exact hroot.hOcc 253
  · exact hroot.hOcc 257
  · exact hroot.hOcc 269
  · exact hroot.hOcc 275
  · exact hroot.hOcc 280
  · exact hroot.hOcc 303
  · exact hroot.hOcc 304
  · exact hroot.hOcc 315
  · exact hroot.hOcc 322
  · exact hroot.hOcc 327
  · exact hroot.hOcc 335
  · exact hroot.hOcc 377
  · exact hroot.hOcc 379
  · exact hroot.hOcc 381
  · exact hroot.hOcc 390
  · exact hroot.hOcc 394
  · exact hroot.hOcc 395
  · exact hroot.hOcc 399
  · exact hroot.hOcc 410
  · exact hroot.hOcc 411
  · exact hroot.hOcc 415
  · exact hroot.hOcc 416
  · exact hroot.hOcc 438
  · exact hroot.hOcc 460
  · exact hroot.hOcc 471
  · exact hroot.hOcc 526
  · exact hroot.hOcc 539
  · exact hroot.hOcc 574
  · exact hroot.hOcc 585
  · exact hroot.hOcc 623
  · exact hroot.hOcc 660
  · exact hroot.hOcc 666
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (7 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (19 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (28 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (29 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (2 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (4 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (10 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
