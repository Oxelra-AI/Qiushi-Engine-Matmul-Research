import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0116Refs : Fin 50 → RowRef 726 49 := ![.occ 94, .occ 107, .occ 112, .occ 152, .occ 171, .occ 198, .occ 206, .occ 255, .occ 275, .occ 299, .occ 323, .occ 350, .occ 359, .occ 363, .occ 382, .occ 422, .occ 484, .occ 486, .occ 503, .occ 509, .occ 529, .occ 531, .occ 543, .occ 568, .occ 601, .occ 606, .occ 631, .occ 632, .occ 640, .occ 652, .occ 653, .occ 662, .occ 665, .occ 687, .occ 722, .occ 723, .sumGe, .nonneg 18, .nonneg 32, .nonneg 33, .nonneg 37, .nonneg 45, .branchGe 31 (1), .branchGe 44 (1), .branchGe 6 (1), .branchGe 15 (1), .branchLe 13 (0), .branchLe 5 (0), .branchLe 23 (0), .branchGe 27 (1)]

def plane491GenLeaf0116Mult : Fin 50 → Nat := ![4315, 4497, 25256, 22155, 11335, 4709, 4818, 18835, 13168, 3155, 9022, 13080, 3089, 18285, 4801, 9585, 2771, 2160, 655, 3131, 251, 14817, 6785, 3062, 5142, 1178, 7266, 92, 6065, 17791, 6707, 3999, 1785, 2166, 3558, 1356, 35025, 7596, 15079, 34815, 421, 3849, 75952, 112869, 31262, 48716, 18153, 27561, 21369, 59873]

theorem plane491GenLeaf0116 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_44 : (1 : Int) ≤ x 44)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0116Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0116Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0116Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0116Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 94
  · exact hroot.hOcc 107
  · exact hroot.hOcc 112
  · exact hroot.hOcc 152
  · exact hroot.hOcc 171
  · exact hroot.hOcc 198
  · exact hroot.hOcc 206
  · exact hroot.hOcc 255
  · exact hroot.hOcc 275
  · exact hroot.hOcc 299
  · exact hroot.hOcc 323
  · exact hroot.hOcc 350
  · exact hroot.hOcc 359
  · exact hroot.hOcc 363
  · exact hroot.hOcc 382
  · exact hroot.hOcc 422
  · exact hroot.hOcc 484
  · exact hroot.hOcc 486
  · exact hroot.hOcc 503
  · exact hroot.hOcc 509
  · exact hroot.hOcc 529
  · exact hroot.hOcc 531
  · exact hroot.hOcc 543
  · exact hroot.hOcc 568
  · exact hroot.hOcc 601
  · exact hroot.hOcc 606
  · exact hroot.hOcc 631
  · exact hroot.hOcc 632
  · exact hroot.hOcc 640
  · exact hroot.hOcc 652
  · exact hroot.hOcc 653
  · exact hroot.hOcc 662
  · exact hroot.hOcc 665
  · exact hroot.hOcc 687
  · exact hroot.hOcc 722
  · exact hroot.hOcc 723
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (18 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (32 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (33 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (37 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (45 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_44
  · change (∑ k, (if k = (6 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (15 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (13 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (5 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (23 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (27 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27

end QiushiMatmul
