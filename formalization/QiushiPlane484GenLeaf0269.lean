import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0269Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 125, .occ 127, .occ 132, .occ 134, .occ 198, .occ 358, .occ 383, .occ 810, .occ 1100, .occ 1132, .occ 1135, .occ 1136, .occ 1151, .occ 1158, .occ 1160, .occ 1220, .occ 1222, .occ 1236, .occ 1287, .occ 1358, .occ 1478, .occ 1481, .occ 1488, .occ 1496, .occ 1638, .occ 1640, .sumGe, .nonneg 11, .nonneg 19, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchGe 29 (1), .branchLe 34 (0), .branchLe 13 (0), .branchLe 37 (0), .branchLe 10 (0), .branchGe 0 (1), .branchLe 25 (0), .branchGe 35 (1), .branchGe 4 (1)]

def plane484GenLeaf0269Mult : Fin 44 → Nat := ![166, 147, 226, 231, 17, 68, 122, 60, 15, 6, 20, 60, 147, 206, 17, 117, 155, 6, 135, 48, 192, 245, 13, 13, 222, 186, 122, 694, 149, 8, 283, 9, 161, 150, 472, 583, 172, 694, 694, 694, 417, 369, 808, 1796]

theorem plane484GenLeaf0269 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0269Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0269Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0269Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0269Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 125
  · exact hroot.hOcc 127
  · exact hroot.hOcc 132
  · exact hroot.hOcc 134
  · exact hroot.hOcc 198
  · exact hroot.hOcc 358
  · exact hroot.hOcc 383
  · exact hroot.hOcc 810
  · exact hroot.hOcc 1100
  · exact hroot.hOcc 1132
  · exact hroot.hOcc 1135
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1222
  · exact hroot.hOcc 1236
  · exact hroot.hOcc 1287
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1638
  · exact hroot.hOcc 1640
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (37 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
