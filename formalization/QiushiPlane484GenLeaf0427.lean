import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0427Refs : Fin 41 → RowRef 1665 43 := ![.occ 126, .occ 127, .occ 129, .occ 136, .occ 137, .occ 139, .occ 153, .occ 174, .occ 213, .occ 233, .occ 561, .occ 780, .occ 876, .occ 1146, .occ 1174, .occ 1196, .occ 1237, .occ 1274, .occ 1294, .occ 1323, .occ 1325, .occ 1326, .occ 1406, .occ 1408, .occ 1478, .occ 1491, .occ 1503, .occ 1508, .occ 1512, .occ 1571, .occ 1623, .sumGe, .nonneg 3, .nonneg 10, .nonneg 12, .nonneg 14, .branchLe 15 (0), .branchGe 2 (1), .branchGe 7 (1), .branchGe 6 (1), .branchGe 33 (1)]

def plane484GenLeaf0427Mult : Fin 41 → Nat := ![4095, 3562, 3674, 616, 1210, 60, 239, 1017, 692, 72, 90, 106, 341, 1285, 114, 1232, 106, 128, 68, 95, 224, 975, 873, 1472, 359, 1285, 419, 950, 446, 1414, 421, 4095, 2570, 2646, 60, 13161, 4095, 7042, 17055, 17765, 5034]

theorem plane484GenLeaf0427 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_33 : (1 : Int) ≤ x 33)
    (hUB_15 : x 15 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0427Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0427Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0427Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0427Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 126
  · exact hroot.hOcc 127
  · exact hroot.hOcc 129
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 139
  · exact hroot.hOcc 153
  · exact hroot.hOcc 174
  · exact hroot.hOcc 213
  · exact hroot.hOcc 233
  · exact hroot.hOcc 561
  · exact hroot.hOcc 780
  · exact hroot.hOcc 876
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1237
  · exact hroot.hOcc 1274
  · exact hroot.hOcc 1294
  · exact hroot.hOcc 1323
  · exact hroot.hOcc 1325
  · exact hroot.hOcc 1326
  · exact hroot.hOcc 1406
  · exact hroot.hOcc 1408
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1503
  · exact hroot.hOcc 1508
  · exact hroot.hOcc 1512
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1623
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (12 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (33 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_33

end QiushiMatmul
