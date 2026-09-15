import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0041Refs : Fin 43 → RowRef 1665 43 := ![.occ 134, .occ 141, .occ 211, .occ 213, .occ 473, .occ 621, .occ 661, .occ 722, .occ 898, .occ 1168, .occ 1213, .occ 1244, .occ 1263, .occ 1267, .occ 1278, .occ 1279, .occ 1304, .occ 1327, .occ 1347, .occ 1357, .occ 1368, .occ 1369, .occ 1387, .occ 1395, .occ 1462, .occ 1472, .occ 1478, .occ 1506, .occ 1556, .occ 1607, .occ 1617, .occ 1648, .occ 1659, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchLe 17 (0), .branchGe 35 (1), .branchGe 25 (1), .branchGe 33 (1)]

def plane484GenLeaf0041Mult : Fin 43 → Nat := ![65, 28, 10, 119, 12, 38, 47, 49, 16, 19, 69, 19, 108, 5, 47, 43, 34, 12, 4, 121, 2, 6, 10, 35, 11, 105, 9, 1, 9, 29, 59, 52, 3, 259, 59, 207, 259, 172, 259, 228, 643, 443, 652]

theorem plane484GenLeaf0041 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hLB_33 : (1 : Int) ≤ x 33)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0041Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0041Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0041Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0041Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 134
  · exact hroot.hOcc 141
  · exact hroot.hOcc 211
  · exact hroot.hOcc 213
  · exact hroot.hOcc 473
  · exact hroot.hOcc 621
  · exact hroot.hOcc 661
  · exact hroot.hOcc 722
  · exact hroot.hOcc 898
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1244
  · exact hroot.hOcc 1263
  · exact hroot.hOcc 1267
  · exact hroot.hOcc 1278
  · exact hroot.hOcc 1279
  · exact hroot.hOcc 1304
  · exact hroot.hOcc 1327
  · exact hroot.hOcc 1347
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1368
  · exact hroot.hOcc 1369
  · exact hroot.hOcc 1387
  · exact hroot.hOcc 1395
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1506
  · exact hroot.hOcc 1556
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1617
  · exact hroot.hOcc 1648
  · exact hroot.hOcc 1659
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25
  · change (∑ k, (if k = (33 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_33

end QiushiMatmul
