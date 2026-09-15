import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0175Refs : Fin 42 → RowRef 1665 43 := ![.occ 119, .occ 121, .occ 126, .occ 132, .occ 134, .occ 139, .occ 141, .occ 168, .occ 259, .occ 494, .occ 638, .occ 1164, .occ 1174, .occ 1216, .occ 1240, .occ 1248, .occ 1258, .occ 1273, .occ 1295, .occ 1312, .occ 1323, .occ 1325, .occ 1343, .occ 1508, .occ 1529, .occ 1542, .occ 1557, .occ 1558, .occ 1625, .occ 1653, .sumGe, .nonneg 0, .nonneg 1, .nonneg 21, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchGe 7 (1), .branchGe 18 (1), .branchLe 42 (0), .branchGe 24 (1)]

def plane484GenLeaf0175Mult : Fin 42 → Nat := ![1347, 614, 535, 1453, 49, 1421, 726, 1729, 291, 719, 1304, 431, 515, 232, 596, 77, 431, 117, 4, 586, 117, 490, 778, 688, 1259, 509, 309, 277, 586, 1135, 3668, 1107, 66, 2306, 2890, 3133, 6328, 3668, 5680, 9259, 3668, 4351]

theorem plane484GenLeaf0175 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0175Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0175Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0175Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0175Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 126
  · exact hroot.hOcc 132
  · exact hroot.hOcc 134
  · exact hroot.hOcc 139
  · exact hroot.hOcc 141
  · exact hroot.hOcc 168
  · exact hroot.hOcc 259
  · exact hroot.hOcc 494
  · exact hroot.hOcc 638
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1240
  · exact hroot.hOcc 1248
  · exact hroot.hOcc 1258
  · exact hroot.hOcc 1273
  · exact hroot.hOcc 1295
  · exact hroot.hOcc 1312
  · exact hroot.hOcc 1323
  · exact hroot.hOcc 1325
  · exact hroot.hOcc 1343
  · exact hroot.hOcc 1508
  · exact hroot.hOcc 1529
  · exact hroot.hOcc 1542
  · exact hroot.hOcc 1557
  · exact hroot.hOcc 1558
  · exact hroot.hOcc 1625
  · exact hroot.hOcc 1653
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24

end QiushiMatmul
