import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0114Refs : Fin 50 → RowRef 726 49 := ![.occ 94, .occ 98, .occ 101, .occ 112, .occ 116, .occ 175, .occ 177, .occ 197, .occ 201, .occ 234, .occ 248, .occ 255, .occ 305, .occ 318, .occ 320, .occ 327, .occ 347, .occ 350, .occ 359, .occ 363, .occ 370, .occ 376, .occ 377, .occ 486, .occ 515, .occ 521, .occ 531, .occ 543, .occ 548, .occ 591, .occ 606, .occ 631, .occ 632, .occ 652, .occ 705, .occ 706, .occ 713, .occ 722, .occ 723, .sumGe, .nonneg 33, .branchGe 31 (1), .branchGe 44 (1), .branchGe 6 (1), .branchGe 15 (1), .branchLe 13 (0), .branchLe 5 (0), .branchLe 23 (0), .branchLe 27 (0), .branchLe 42 (0)]

def plane491GenLeaf0114Mult : Fin 50 → Nat := ![1888, 3112, 440, 1240, 266, 1178, 672, 1730, 2196, 890, 582, 1710, 316, 708, 624, 216, 232, 753, 792, 651, 540, 372, 103, 350, 1044, 219, 2530, 266, 498, 190, 232, 728, 190, 1380, 2172, 212, 898, 358, 2088, 6098, 2824, 12516, 12524, 6134, 2244, 6098, 5866, 5152, 4146, 6098]

theorem plane491GenLeaf0114 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_44 : (1 : Int) ≤ x 44)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0114Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0114Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0114Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0114Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 94
  · exact hroot.hOcc 98
  · exact hroot.hOcc 101
  · exact hroot.hOcc 112
  · exact hroot.hOcc 116
  · exact hroot.hOcc 175
  · exact hroot.hOcc 177
  · exact hroot.hOcc 197
  · exact hroot.hOcc 201
  · exact hroot.hOcc 234
  · exact hroot.hOcc 248
  · exact hroot.hOcc 255
  · exact hroot.hOcc 305
  · exact hroot.hOcc 318
  · exact hroot.hOcc 320
  · exact hroot.hOcc 327
  · exact hroot.hOcc 347
  · exact hroot.hOcc 350
  · exact hroot.hOcc 359
  · exact hroot.hOcc 363
  · exact hroot.hOcc 370
  · exact hroot.hOcc 376
  · exact hroot.hOcc 377
  · exact hroot.hOcc 486
  · exact hroot.hOcc 515
  · exact hroot.hOcc 521
  · exact hroot.hOcc 531
  · exact hroot.hOcc 543
  · exact hroot.hOcc 548
  · exact hroot.hOcc 591
  · exact hroot.hOcc 606
  · exact hroot.hOcc 631
  · exact hroot.hOcc 632
  · exact hroot.hOcc 652
  · exact hroot.hOcc 705
  · exact hroot.hOcc 706
  · exact hroot.hOcc 713
  · exact hroot.hOcc 722
  · exact hroot.hOcc 723
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (33 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_44
  · change (∑ k, (if k = (6 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (15 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (13 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (5 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (23 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (42 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42

end QiushiMatmul
