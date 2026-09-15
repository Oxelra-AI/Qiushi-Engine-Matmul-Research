import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0086Refs : Fin 50 → RowRef 726 49 := ![.occ 98, .occ 100, .occ 118, .occ 153, .occ 161, .occ 193, .occ 254, .occ 312, .occ 320, .occ 323, .occ 329, .occ 332, .occ 334, .occ 350, .occ 359, .occ 368, .occ 373, .occ 409, .occ 410, .occ 416, .occ 469, .occ 482, .occ 484, .occ 485, .occ 496, .occ 517, .occ 523, .occ 524, .occ 526, .occ 538, .occ 541, .occ 567, .occ 571, .occ 582, .occ 601, .occ 606, .occ 640, .occ 644, .occ 658, .occ 665, .sumGe, .nonneg 7, .nonneg 37, .branchGe 31 (1), .branchLe 44 (0), .branchLe 11 (0), .branchGe 27 (1), .branchGe 43 (1), .branchLe 42 (0), .branchLe 38 (0)]

def plane491GenLeaf0086Mult : Fin 50 → Nat := ![1929, 9793, 7850, 7633, 2294, 4740, 784, 6555, 5024, 2539, 3431, 2560, 391, 12525, 847, 827, 3618, 1284, 3692, 2800, 344, 4389, 610, 6339, 631, 2279, 979, 1124, 8, 490, 1733, 1651, 266, 4473, 3195, 3257, 833, 4141, 1825, 1124, 17790, 570, 10588, 43034, 16957, 16057, 45481, 18975, 16400, 15251]

theorem plane491GenLeaf0086 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_43 : (1 : Int) ≤ x 43)
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0086Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0086Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0086Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0086Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 98
  · exact hroot.hOcc 100
  · exact hroot.hOcc 118
  · exact hroot.hOcc 153
  · exact hroot.hOcc 161
  · exact hroot.hOcc 193
  · exact hroot.hOcc 254
  · exact hroot.hOcc 312
  · exact hroot.hOcc 320
  · exact hroot.hOcc 323
  · exact hroot.hOcc 329
  · exact hroot.hOcc 332
  · exact hroot.hOcc 334
  · exact hroot.hOcc 350
  · exact hroot.hOcc 359
  · exact hroot.hOcc 368
  · exact hroot.hOcc 373
  · exact hroot.hOcc 409
  · exact hroot.hOcc 410
  · exact hroot.hOcc 416
  · exact hroot.hOcc 469
  · exact hroot.hOcc 482
  · exact hroot.hOcc 484
  · exact hroot.hOcc 485
  · exact hroot.hOcc 496
  · exact hroot.hOcc 517
  · exact hroot.hOcc 523
  · exact hroot.hOcc 524
  · exact hroot.hOcc 526
  · exact hroot.hOcc 538
  · exact hroot.hOcc 541
  · exact hroot.hOcc 567
  · exact hroot.hOcc 571
  · exact hroot.hOcc 582
  · exact hroot.hOcc 601
  · exact hroot.hOcc 606
  · exact hroot.hOcc 640
  · exact hroot.hOcc 644
  · exact hroot.hOcc 658
  · exact hroot.hOcc 665
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (37 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (11 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (27 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (43 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_43
  · change (∑ k, (if k = (42 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (38 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38

end QiushiMatmul
