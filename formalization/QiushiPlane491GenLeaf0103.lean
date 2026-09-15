import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0103Refs : Fin 50 → RowRef 726 49 := ![.occ 78, .occ 80, .occ 98, .occ 112, .occ 123, .occ 146, .occ 171, .occ 195, .occ 196, .occ 198, .occ 214, .occ 223, .occ 230, .occ 231, .occ 275, .occ 299, .occ 304, .occ 331, .occ 337, .occ 351, .occ 363, .occ 370, .occ 382, .occ 393, .occ 396, .occ 400, .occ 404, .occ 422, .occ 425, .occ 531, .occ 554, .occ 565, .occ 583, .occ 584, .occ 586, .occ 618, .occ 630, .occ 664, .occ 700, .occ 722, .sumGe, .nonneg 33, .branchGe 31 (1), .branchGe 44 (1), .branchLe 6 (0), .branchLe 39 (0), .branchGe 28 (1), .branchLe 36 (0), .branchGe 15 (1), .branchGe 9 (1)]

def plane491GenLeaf0103Mult : Fin 50 → Nat := ![11883, 13907, 16579, 12313, 72, 1408, 1033, 859, 8645, 2125, 5025, 1385, 8045, 2623, 5512, 11038, 806, 1715, 2153, 9806, 1594, 5848, 1944, 1704, 236, 3275, 162, 2327, 3775, 7221, 2224, 1508, 236, 1668, 2271, 695, 4992, 5318, 2274, 8209, 21313, 3600, 26335, 45723, 21313, 19089, 27067, 9913, 3304, 61603]

theorem plane491GenLeaf0103 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_44 : (1 : Int) ≤ x 44)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0103Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0103Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0103Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0103Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 78
  · exact hroot.hOcc 80
  · exact hroot.hOcc 98
  · exact hroot.hOcc 112
  · exact hroot.hOcc 123
  · exact hroot.hOcc 146
  · exact hroot.hOcc 171
  · exact hroot.hOcc 195
  · exact hroot.hOcc 196
  · exact hroot.hOcc 198
  · exact hroot.hOcc 214
  · exact hroot.hOcc 223
  · exact hroot.hOcc 230
  · exact hroot.hOcc 231
  · exact hroot.hOcc 275
  · exact hroot.hOcc 299
  · exact hroot.hOcc 304
  · exact hroot.hOcc 331
  · exact hroot.hOcc 337
  · exact hroot.hOcc 351
  · exact hroot.hOcc 363
  · exact hroot.hOcc 370
  · exact hroot.hOcc 382
  · exact hroot.hOcc 393
  · exact hroot.hOcc 396
  · exact hroot.hOcc 400
  · exact hroot.hOcc 404
  · exact hroot.hOcc 422
  · exact hroot.hOcc 425
  · exact hroot.hOcc 531
  · exact hroot.hOcc 554
  · exact hroot.hOcc 565
  · exact hroot.hOcc 583
  · exact hroot.hOcc 584
  · exact hroot.hOcc 586
  · exact hroot.hOcc 618
  · exact hroot.hOcc 630
  · exact hroot.hOcc 664
  · exact hroot.hOcc 700
  · exact hroot.hOcc 722
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (33 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_44
  · change (∑ k, (if k = (6 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (39 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (28 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (36 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (15 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (9 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9

end QiushiMatmul
