import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0023Refs : Fin 44 → RowRef 1665 43 := ![.occ 92, .occ 119, .occ 126, .occ 127, .occ 139, .occ 140, .occ 144, .occ 233, .occ 327, .occ 562, .occ 633, .occ 840, .occ 1122, .occ 1164, .occ 1166, .occ 1196, .occ 1208, .occ 1221, .occ 1223, .occ 1272, .occ 1273, .occ 1275, .occ 1347, .occ 1357, .occ 1462, .occ 1508, .occ 1511, .occ 1597, .occ 1634, .occ 1650, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchLe 17 (0), .branchGe 35 (1), .branchLe 25 (0), .branchLe 18 (0), .branchLe 42 (0), .branchLe 5 (0), .branchLe 19 (0), .branchGe 7 (1)]

def plane484GenLeaf0023Mult : Fin 44 → Nat := ![912, 2602, 1083, 2160, 898, 78, 203, 2850, 365, 279, 1915, 4023, 112, 2037, 645, 2805, 1928, 466, 144, 429, 158, 261, 732, 732, 383, 250, 279, 244, 1162, 122, 6016, 5677, 854, 2897, 1132, 5691, 4618, 5420, 6016, 2674, 4471, 4837, 4286, 18904]

theorem plane484GenLeaf0023 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0023Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0023Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0023Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0023Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 92
  · exact hroot.hOcc 119
  · exact hroot.hOcc 126
  · exact hroot.hOcc 127
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 144
  · exact hroot.hOcc 233
  · exact hroot.hOcc 327
  · exact hroot.hOcc 562
  · exact hroot.hOcc 633
  · exact hroot.hOcc 840
  · exact hroot.hOcc 1122
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1221
  · exact hroot.hOcc 1223
  · exact hroot.hOcc 1272
  · exact hroot.hOcc 1273
  · exact hroot.hOcc 1275
  · exact hroot.hOcc 1347
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1508
  · exact hroot.hOcc 1511
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1634
  · exact hroot.hOcc 1650
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7

end QiushiMatmul
