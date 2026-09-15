import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0256Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 127, .occ 133, .occ 136, .occ 141, .occ 211, .occ 858, .occ 1143, .occ 1145, .occ 1160, .occ 1168, .occ 1188, .occ 1190, .occ 1191, .occ 1213, .occ 1253, .occ 1284, .occ 1366, .occ 1367, .occ 1390, .occ 1435, .occ 1470, .occ 1481, .occ 1506, .occ 1514, .occ 1553, .occ 1610, .occ 1625, .sumGe, .nonneg 16, .nonneg 19, .nonneg 24, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchLe 29 (0), .branchGe 17 (1), .branchLe 3 (0), .branchLe 20 (0), .branchLe 8 (0), .branchLe 13 (0), .branchGe 25 (1)]

def plane484GenLeaf0256Mult : Fin 44 → Nat := ![774, 2991, 6090, 10966, 4668, 248, 1830, 3046, 1177, 388, 2018, 641, 2438, 867, 1564, 1186, 1793, 126, 2851, 677, 2178, 321, 3364, 112, 1253, 1153, 1575, 1417, 10966, 6990, 20332, 6053, 1152, 13363, 6722, 1519, 2863, 5797, 30883, 9425, 3051, 10645, 4297, 31468]

theorem plane484GenLeaf0256 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0256Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0256Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0256Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0256Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 127
  · exact hroot.hOcc 133
  · exact hroot.hOcc 136
  · exact hroot.hOcc 141
  · exact hroot.hOcc 211
  · exact hroot.hOcc 858
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1253
  · exact hroot.hOcc 1284
  · exact hroot.hOcc 1366
  · exact hroot.hOcc 1367
  · exact hroot.hOcc 1390
  · exact hroot.hOcc 1435
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1506
  · exact hroot.hOcc 1514
  · exact hroot.hOcc 1553
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1625
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25

end QiushiMatmul
