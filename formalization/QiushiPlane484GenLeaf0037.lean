import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0037Refs : Fin 43 → RowRef 1665 43 := ![.occ 121, .occ 133, .occ 134, .occ 142, .occ 211, .occ 616, .occ 696, .occ 710, .occ 803, .occ 858, .occ 978, .occ 981, .occ 1133, .occ 1213, .occ 1260, .occ 1268, .occ 1278, .occ 1280, .occ 1304, .occ 1350, .occ 1367, .occ 1409, .occ 1489, .occ 1514, .occ 1527, .occ 1564, .occ 1608, .occ 1657, .occ 1658, .sumGe, .nonneg 15, .nonneg 16, .nonneg 17, .nonneg 18, .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchGe 35 (1), .branchGe 25 (1), .branchLe 33 (0), .branchLe 10 (0), .branchGe 21 (1)]

def plane484GenLeaf0037Mult : Fin 43 → Nat := ![42, 269, 92, 573, 156, 12, 133, 123, 19, 564, 22, 170, 88, 200, 7, 23, 37, 60, 263, 200, 366, 42, 23, 247, 53, 234, 161, 32, 11, 734, 1892, 23, 7, 124, 147, 734, 734, 642, 1232, 3192, 455, 674, 2111]

theorem plane484GenLeaf0037 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0037Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0037Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0037Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0037Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 133
  · exact hroot.hOcc 134
  · exact hroot.hOcc 142
  · exact hroot.hOcc 211
  · exact hroot.hOcc 616
  · exact hroot.hOcc 696
  · exact hroot.hOcc 710
  · exact hroot.hOcc 803
  · exact hroot.hOcc 858
  · exact hroot.hOcc 978
  · exact hroot.hOcc 981
  · exact hroot.hOcc 1133
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1260
  · exact hroot.hOcc 1268
  · exact hroot.hOcc 1278
  · exact hroot.hOcc 1280
  · exact hroot.hOcc 1304
  · exact hroot.hOcc 1350
  · exact hroot.hOcc 1367
  · exact hroot.hOcc 1409
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1514
  · exact hroot.hOcc 1527
  · exact hroot.hOcc 1564
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1657
  · exact hroot.hOcc 1658
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25
  · change (∑ k, (if k = (33 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21

end QiushiMatmul
