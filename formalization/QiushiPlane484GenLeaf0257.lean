import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0257Refs : Fin 44 → RowRef 1665 43 := ![.occ 121, .occ 122, .occ 123, .occ 130, .occ 132, .occ 133, .occ 176, .occ 568, .occ 614, .occ 1133, .occ 1143, .occ 1150, .occ 1172, .occ 1173, .occ 1191, .occ 1234, .occ 1260, .occ 1280, .occ 1322, .occ 1338, .occ 1369, .occ 1413, .occ 1435, .occ 1481, .occ 1483, .occ 1567, .occ 1609, .occ 1624, .sumGe, .nonneg 4, .nonneg 12, .nonneg 16, .nonneg 22, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchLe 29 (0), .branchGe 17 (1), .branchLe 3 (0), .branchLe 20 (0), .branchLe 8 (0), .branchGe 13 (1)]

def plane484GenLeaf0257Mult : Fin 44 → Nat := ![2271, 2034, 451, 1742, 77, 504, 1921, 663, 3215, 150, 265, 371, 950, 354, 2801, 358, 383, 106, 229, 161, 204, 272, 1090, 284, 2484, 431, 996, 1211, 5330, 172, 567, 1401, 477, 2086, 4601, 1465, 2343, 5330, 4615, 9058, 7, 5330, 1634, 13526]

theorem plane484GenLeaf0257 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0257Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0257Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0257Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0257Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 130
  · exact hroot.hOcc 132
  · exact hroot.hOcc 133
  · exact hroot.hOcc 176
  · exact hroot.hOcc 568
  · exact hroot.hOcc 614
  · exact hroot.hOcc 1133
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1234
  · exact hroot.hOcc 1260
  · exact hroot.hOcc 1280
  · exact hroot.hOcc 1322
  · exact hroot.hOcc 1338
  · exact hroot.hOcc 1369
  · exact hroot.hOcc 1413
  · exact hroot.hOcc 1435
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1624
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (12 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
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
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13

end QiushiMatmul
