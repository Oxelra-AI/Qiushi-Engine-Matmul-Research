import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0413Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 124, .occ 136, .occ 137, .occ 213, .occ 260, .occ 441, .occ 562, .occ 1028, .occ 1164, .occ 1168, .occ 1174, .occ 1183, .occ 1187, .occ 1191, .occ 1208, .occ 1220, .occ 1347, .occ 1358, .occ 1444, .occ 1448, .occ 1458, .occ 1470, .occ 1486, .occ 1534, .occ 1608, .occ 1615, .occ 1628, .occ 1657, .sumGe, .nonneg 1, .nonneg 4, .nonneg 17, .nonneg 20, .nonneg 22, .branchLe 15 (0), .branchGe 2 (1), .branchGe 7 (1), .branchLe 6 (0), .branchGe 31 (1), .branchLe 29 (0), .branchLe 14 (0), .branchLe 24 (0), .branchGe 16 (1)]

def plane484GenLeaf0413Mult : Fin 44 → Nat := ![4950, 3648, 3890, 6780, 820, 76, 5320, 1128, 1652, 59, 364, 2496, 1489, 1312, 1102, 2110, 1122, 1312, 2171, 170, 400, 210, 2818, 3073, 982, 2253, 473, 1995, 1803, 11392, 40, 420, 380, 2096, 908, 8748, 9902, 23032, 11392, 5748, 8260, 11392, 5448, 23912]

theorem plane484GenLeaf0413 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0413Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0413Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0413Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0413Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 124
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 213
  · exact hroot.hOcc 260
  · exact hroot.hOcc 441
  · exact hroot.hOcc 562
  · exact hroot.hOcc 1028
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1347
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1444
  · exact hroot.hOcc 1448
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1534
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1628
  · exact hroot.hOcc 1657
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16

end QiushiMatmul
