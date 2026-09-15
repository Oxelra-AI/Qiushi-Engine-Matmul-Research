import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0040Refs : Fin 49 → RowRef 668 48 := ![.occ 83, .occ 99, .occ 104, .occ 123, .occ 137, .occ 139, .occ 195, .occ 237, .occ 241, .occ 275, .occ 280, .occ 294, .occ 298, .occ 303, .occ 304, .occ 311, .occ 313, .occ 315, .occ 335, .occ 356, .occ 386, .occ 391, .occ 399, .occ 404, .occ 415, .occ 449, .occ 454, .occ 473, .occ 497, .occ 526, .occ 531, .occ 539, .occ 557, .occ 581, .occ 606, .occ 621, .occ 631, .occ 634, .occ 644, .occ 645, .occ 660, .occ 666, .sumGe, .nonneg 22, .branchLe 39 (0), .branchGe 23 (1), .branchLe 2 (0), .branchLe 4 (0), .branchGe 46 (1)]

def plane487GenLeaf0040Mult : Fin 49 → Nat := ![3758830, 1053632, 10430290, 461780, 3406122, 8252608, 4990936, 6599416, 4769822, 2116778, 3214304, 843320, 2961102, 282140, 6231064, 2009940, 5426342, 10625500, 5842418, 1088818, 3451984, 4431360, 735592, 1139090, 3767130, 88282, 417388, 1752696, 636976, 2286876, 2093788, 6502672, 1383034, 1740562, 2110708, 982242, 269378, 319332, 1438573, 364865, 1288767, 2869481, 18597126, 3957982, 14506812, 62863878, 18597126, 6953964, 29785158]

theorem plane487GenLeaf0040 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_46 : (1 : Int) ≤ x 46)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0040Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0040Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0040Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0040Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 83
  · exact hroot.hOcc 99
  · exact hroot.hOcc 104
  · exact hroot.hOcc 123
  · exact hroot.hOcc 137
  · exact hroot.hOcc 139
  · exact hroot.hOcc 195
  · exact hroot.hOcc 237
  · exact hroot.hOcc 241
  · exact hroot.hOcc 275
  · exact hroot.hOcc 280
  · exact hroot.hOcc 294
  · exact hroot.hOcc 298
  · exact hroot.hOcc 303
  · exact hroot.hOcc 304
  · exact hroot.hOcc 311
  · exact hroot.hOcc 313
  · exact hroot.hOcc 315
  · exact hroot.hOcc 335
  · exact hroot.hOcc 356
  · exact hroot.hOcc 386
  · exact hroot.hOcc 391
  · exact hroot.hOcc 399
  · exact hroot.hOcc 404
  · exact hroot.hOcc 415
  · exact hroot.hOcc 449
  · exact hroot.hOcc 454
  · exact hroot.hOcc 473
  · exact hroot.hOcc 497
  · exact hroot.hOcc 526
  · exact hroot.hOcc 531
  · exact hroot.hOcc 539
  · exact hroot.hOcc 557
  · exact hroot.hOcc 581
  · exact hroot.hOcc 606
  · exact hroot.hOcc 621
  · exact hroot.hOcc 631
  · exact hroot.hOcc 634
  · exact hroot.hOcc 644
  · exact hroot.hOcc 645
  · exact hroot.hOcc 660
  · exact hroot.hOcc 666
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (22 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (2 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (4 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (46 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_46

end QiushiMatmul
