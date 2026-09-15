import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0104Refs : Fin 50 → RowRef 726 49 := ![.occ 101, .occ 105, .occ 112, .occ 113, .occ 169, .occ 196, .occ 211, .occ 237, .occ 244, .occ 257, .occ 287, .occ 319, .occ 329, .occ 350, .occ 351, .occ 359, .occ 363, .occ 381, .occ 393, .occ 394, .occ 398, .occ 404, .occ 408, .occ 421, .occ 425, .occ 430, .occ 484, .occ 495, .occ 531, .occ 544, .occ 566, .occ 586, .occ 624, .occ 632, .occ 653, .occ 662, .occ 686, .occ 691, .occ 722, .occ 723, .sumGe, .nonneg 30, .nonneg 33, .nonneg 46, .branchGe 31 (1), .branchGe 44 (1), .branchLe 6 (0), .branchLe 39 (0), .branchGe 28 (1), .branchGe 36 (1)]

def plane491GenLeaf0104Mult : Fin 50 → Nat := ![5698, 13879, 8487, 3635, 2306, 2210, 366, 1664, 1972, 4602, 2440, 4615, 6029, 1030, 74, 8714, 10682, 1127, 36, 2186, 1080, 5263, 2883, 4815, 2439, 766, 916, 1297, 5712, 2622, 2131, 1950, 2822, 1792, 449, 1539, 490, 4929, 1418, 732, 15371, 2087, 12126, 11030, 29189, 42354, 13130, 8413, 24471, 48969]

theorem plane491GenLeaf0104 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_44 : (1 : Int) ≤ x 44)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0104Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0104Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0104Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0104Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 101
  · exact hroot.hOcc 105
  · exact hroot.hOcc 112
  · exact hroot.hOcc 113
  · exact hroot.hOcc 169
  · exact hroot.hOcc 196
  · exact hroot.hOcc 211
  · exact hroot.hOcc 237
  · exact hroot.hOcc 244
  · exact hroot.hOcc 257
  · exact hroot.hOcc 287
  · exact hroot.hOcc 319
  · exact hroot.hOcc 329
  · exact hroot.hOcc 350
  · exact hroot.hOcc 351
  · exact hroot.hOcc 359
  · exact hroot.hOcc 363
  · exact hroot.hOcc 381
  · exact hroot.hOcc 393
  · exact hroot.hOcc 394
  · exact hroot.hOcc 398
  · exact hroot.hOcc 404
  · exact hroot.hOcc 408
  · exact hroot.hOcc 421
  · exact hroot.hOcc 425
  · exact hroot.hOcc 430
  · exact hroot.hOcc 484
  · exact hroot.hOcc 495
  · exact hroot.hOcc 531
  · exact hroot.hOcc 544
  · exact hroot.hOcc 566
  · exact hroot.hOcc 586
  · exact hroot.hOcc 624
  · exact hroot.hOcc 632
  · exact hroot.hOcc 653
  · exact hroot.hOcc 662
  · exact hroot.hOcc 686
  · exact hroot.hOcc 691
  · exact hroot.hOcc 722
  · exact hroot.hOcc 723
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (30 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (33 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (46 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_44
  · change (∑ k, (if k = (6 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (39 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (28 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (36 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36

end QiushiMatmul
