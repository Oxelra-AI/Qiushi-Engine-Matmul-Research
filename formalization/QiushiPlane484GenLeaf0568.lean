import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0568Refs : Fin 43 → RowRef 1665 43 := ![.occ 133, .occ 142, .occ 155, .occ 199, .occ 213, .occ 285, .occ 292, .occ 471, .occ 552, .occ 559, .occ 572, .occ 640, .occ 711, .occ 858, .occ 1168, .occ 1259, .occ 1265, .occ 1298, .occ 1299, .occ 1318, .occ 1339, .occ 1350, .occ 1385, .occ 1417, .occ 1431, .occ 1467, .occ 1492, .occ 1496, .occ 1543, .occ 1550, .occ 1563, .occ 1607, .occ 1615, .occ 1623, .occ 1649, .sumGe, .nonneg 17, .nonneg 21, .branchGe 15 (1), .branchGe 35 (1), .branchGe 25 (1), .branchGe 29 (1), .branchGe 32 (1)]

def plane484GenLeaf0568Mult : Fin 43 → Nat := ![1022, 698, 927, 59, 244, 210, 1197, 217, 457, 751, 1034, 2, 40, 767, 271, 316, 401, 59, 59, 338, 59, 468, 35, 54, 151, 118, 826, 59, 271, 462, 112, 198, 171, 314, 512, 1652, 118, 2803, 5389, 4088, 7997, 5174, 5758]

theorem plane484GenLeaf0568 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hLB_35 : (1 : Int) ≤ x 35)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0568Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0568Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0568Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0568Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 133
  · exact hroot.hOcc 142
  · exact hroot.hOcc 155
  · exact hroot.hOcc 199
  · exact hroot.hOcc 213
  · exact hroot.hOcc 285
  · exact hroot.hOcc 292
  · exact hroot.hOcc 471
  · exact hroot.hOcc 552
  · exact hroot.hOcc 559
  · exact hroot.hOcc 572
  · exact hroot.hOcc 640
  · exact hroot.hOcc 711
  · exact hroot.hOcc 858
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1259
  · exact hroot.hOcc 1265
  · exact hroot.hOcc 1298
  · exact hroot.hOcc 1299
  · exact hroot.hOcc 1318
  · exact hroot.hOcc 1339
  · exact hroot.hOcc 1350
  · exact hroot.hOcc 1385
  · exact hroot.hOcc 1417
  · exact hroot.hOcc 1431
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1543
  · exact hroot.hOcc 1550
  · exact hroot.hOcc 1563
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1623
  · exact hroot.hOcc 1649
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (32 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32

end QiushiMatmul
