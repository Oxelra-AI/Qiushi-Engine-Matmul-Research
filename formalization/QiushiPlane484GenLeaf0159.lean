import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0159Refs : Fin 44 → RowRef 1665 43 := ![.occ 123, .occ 126, .occ 127, .occ 129, .occ 132, .occ 144, .occ 271, .occ 385, .occ 386, .occ 404, .occ 440, .occ 695, .occ 1151, .occ 1271, .occ 1273, .occ 1283, .occ 1352, .occ 1389, .occ 1404, .occ 1477, .occ 1478, .occ 1503, .occ 1508, .occ 1511, .occ 1512, .occ 1529, .occ 1549, .occ 1636, .occ 1660, .sumGe, .nonneg 1, .nonneg 2, .nonneg 11, .nonneg 13, .nonneg 14, .branchLe 15 (0), .branchGe 29 (1), .branchLe 35 (0), .branchGe 7 (1), .branchLe 18 (0), .branchLe 30 (0), .branchGe 21 (1), .branchLe 25 (0), .branchGe 6 (1)]

def plane484GenLeaf0159Mult : Fin 44 → Nat := ![332, 692, 179, 847, 288, 100, 705, 166, 121, 51, 177, 55, 474, 495, 209, 26, 81, 373, 336, 96, 249, 70, 90, 272, 59, 26, 100, 81, 44, 1179, 85, 47, 100, 207, 1664, 640, 1621, 930, 2148, 539, 1179, 1447, 1179, 4369]

theorem plane484GenLeaf0159 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0159Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0159Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0159Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0159Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 123
  · exact hroot.hOcc 126
  · exact hroot.hOcc 127
  · exact hroot.hOcc 129
  · exact hroot.hOcc 132
  · exact hroot.hOcc 144
  · exact hroot.hOcc 271
  · exact hroot.hOcc 385
  · exact hroot.hOcc 386
  · exact hroot.hOcc 404
  · exact hroot.hOcc 440
  · exact hroot.hOcc 695
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1271
  · exact hroot.hOcc 1273
  · exact hroot.hOcc 1283
  · exact hroot.hOcc 1352
  · exact hroot.hOcc 1389
  · exact hroot.hOcc 1404
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1503
  · exact hroot.hOcc 1508
  · exact hroot.hOcc 1511
  · exact hroot.hOcc 1512
  · exact hroot.hOcc 1529
  · exact hroot.hOcc 1549
  · exact hroot.hOcc 1636
  · exact hroot.hOcc 1660
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6

end QiushiMatmul
