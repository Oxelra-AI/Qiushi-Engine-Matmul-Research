import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0350Refs : Fin 44 → RowRef 1665 43 := ![.occ 125, .occ 128, .occ 130, .occ 137, .occ 139, .occ 401, .occ 408, .occ 411, .occ 707, .occ 816, .occ 818, .occ 1154, .occ 1168, .occ 1172, .occ 1173, .occ 1179, .occ 1187, .occ 1190, .occ 1200, .occ 1215, .occ 1230, .occ 1387, .occ 1462, .occ 1471, .occ 1491, .occ 1509, .occ 1538, .occ 1557, .occ 1571, .occ 1601, .occ 1638, .sumGe, .nonneg 16, .nonneg 24, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchGe 26 (1), .branchGe 14 (1), .branchGe 36 (1), .branchGe 30 (1), .branchLe 12 (0), .branchGe 40 (1)]

def plane484GenLeaf0350Mult : Fin 44 → Nat := ![24052, 5738, 14833, 4856, 19888, 8683, 5372, 780, 5656, 9565, 15126, 1033, 2886, 177, 18008, 1651, 441, 2380, 16426, 2101, 4022, 11756, 11926, 592, 16936, 25993, 3694, 367, 11164, 1369, 350, 42929, 915, 8272, 26503, 33676, 5772, 32400, 70270, 108498, 23355, 79474, 21234, 67559]

theorem plane484GenLeaf0350 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hLB_40 : (1 : Int) ≤ x 40)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0350Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0350Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0350Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0350Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 125
  · exact hroot.hOcc 128
  · exact hroot.hOcc 130
  · exact hroot.hOcc 137
  · exact hroot.hOcc 139
  · exact hroot.hOcc 401
  · exact hroot.hOcc 408
  · exact hroot.hOcc 411
  · exact hroot.hOcc 707
  · exact hroot.hOcc 816
  · exact hroot.hOcc 818
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1230
  · exact hroot.hOcc 1387
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1509
  · exact hroot.hOcc 1538
  · exact hroot.hOcc 1557
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1638
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (36 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (12 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (40 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_40

end QiushiMatmul
