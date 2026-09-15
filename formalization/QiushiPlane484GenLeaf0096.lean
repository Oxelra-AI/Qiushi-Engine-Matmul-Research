import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0096Refs : Fin 42 → RowRef 1665 43 := ![.occ 120, .occ 121, .occ 137, .occ 139, .occ 141, .occ 193, .occ 352, .occ 369, .occ 408, .occ 515, .occ 652, .occ 812, .occ 1019, .occ 1146, .occ 1168, .occ 1229, .occ 1270, .occ 1401, .occ 1437, .occ 1441, .occ 1448, .occ 1449, .occ 1478, .occ 1547, .occ 1573, .occ 1617, .occ 1626, .occ 1659, .occ 1663, .sumGe, .nonneg 16, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchGe 4 (1), .branchLe 36 (0), .branchGe 26 (1), .branchLe 37 (0), .branchGe 28 (1), .branchLe 8 (0), .branchLe 13 (0), .branchLe 14 (0)]

def plane484GenLeaf0096Mult : Fin 42 → Nat := ![538, 914, 426, 1150, 900, 694, 662, 22, 10, 154, 542, 378, 44, 1014, 460, 346, 164, 92, 40, 402, 622, 146, 388, 738, 460, 75, 95, 281, 103, 2452, 504, 1658, 552, 2452, 2798, 1492, 4104, 2452, 2864, 2128, 1096, 2106]

theorem plane484GenLeaf0096 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0096Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0096Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0096Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0096Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 121
  · exact hroot.hOcc 137
  · exact hroot.hOcc 139
  · exact hroot.hOcc 141
  · exact hroot.hOcc 193
  · exact hroot.hOcc 352
  · exact hroot.hOcc 369
  · exact hroot.hOcc 408
  · exact hroot.hOcc 515
  · exact hroot.hOcc 652
  · exact hroot.hOcc 812
  · exact hroot.hOcc 1019
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1229
  · exact hroot.hOcc 1270
  · exact hroot.hOcc 1401
  · exact hroot.hOcc 1437
  · exact hroot.hOcc 1441
  · exact hroot.hOcc 1448
  · exact hroot.hOcc 1449
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1547
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1617
  · exact hroot.hOcc 1626
  · exact hroot.hOcc 1659
  · exact hroot.hOcc 1663
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (37 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14

end QiushiMatmul
