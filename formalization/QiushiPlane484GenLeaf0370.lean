import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0370Refs : Fin 44 → RowRef 1665 43 := ![.occ 128, .occ 130, .occ 131, .occ 132, .occ 133, .occ 134, .occ 144, .occ 145, .occ 149, .occ 288, .occ 325, .occ 386, .occ 435, .occ 752, .occ 1136, .occ 1146, .occ 1154, .occ 1183, .occ 1228, .occ 1232, .occ 1290, .occ 1322, .occ 1358, .occ 1458, .occ 1459, .occ 1471, .occ 1490, .occ 1491, .occ 1597, .occ 1601, .occ 1603, .occ 1633, .sumGe, .nonneg 12, .nonneg 14, .nonneg 15, .branchGe 2 (1), .branchLe 7 (0), .branchGe 23 (1), .branchLe 35 (0), .branchGe 3 (1), .branchLe 9 (0), .branchGe 1 (1), .branchGe 0 (1)]

def plane484GenLeaf0370Mult : Fin 44 → Nat := ![2503, 867, 1394, 1102, 870, 888, 941, 1115, 370, 1728, 882, 444, 840, 412, 608, 1982, 338, 264, 166, 12, 170, 616, 1062, 68, 670, 34, 372, 1326, 40, 494, 304, 142, 3822, 100, 196, 528, 1590, 1360, 8936, 3782, 11206, 1232, 2530, 3124]

theorem plane484GenLeaf0370 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0370Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0370Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0370Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0370Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 128
  · exact hroot.hOcc 130
  · exact hroot.hOcc 131
  · exact hroot.hOcc 132
  · exact hroot.hOcc 133
  · exact hroot.hOcc 134
  · exact hroot.hOcc 144
  · exact hroot.hOcc 145
  · exact hroot.hOcc 149
  · exact hroot.hOcc 288
  · exact hroot.hOcc 325
  · exact hroot.hOcc 386
  · exact hroot.hOcc 435
  · exact hroot.hOcc 752
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1228
  · exact hroot.hOcc 1232
  · exact hroot.hOcc 1290
  · exact hroot.hOcc 1322
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1490
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1633
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (12 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3
  · change (∑ k, (if k = (9 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
