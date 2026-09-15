import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0201Refs : Fin 44 → RowRef 1665 43 := ![.occ 122, .occ 128, .occ 133, .occ 220, .occ 440, .occ 647, .occ 661, .occ 888, .occ 928, .occ 1140, .occ 1161, .occ 1164, .occ 1173, .occ 1179, .occ 1196, .occ 1203, .occ 1214, .occ 1220, .occ 1279, .occ 1293, .occ 1300, .occ 1341, .occ 1373, .occ 1375, .occ 1462, .occ 1472, .occ 1478, .occ 1580, .occ 1607, .occ 1632, .occ 1650, .sumGe, .nonneg 17, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchGe 35 (1), .branchLe 16 (0), .branchLe 18 (0), .branchGe 1 (1), .branchLe 22 (0), .branchGe 21 (1), .branchLe 31 (0), .branchGe 33 (1)]

def plane484GenLeaf0201Mult : Fin 44 → Nat := ![4994, 1057, 4975, 17248, 2419, 6972, 3968, 4187, 3695, 1736, 4492, 1757, 5187, 1900, 661, 8, 3630, 3048, 719, 7609, 1265, 5470, 965, 537, 2253, 8019, 2174, 1381, 3300, 536, 1206, 17784, 1821, 4473, 17123, 23653, 58654, 16042, 9748, 16085, 4187, 52189, 15884, 47564]

theorem plane484GenLeaf0201 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_33 : (1 : Int) ≤ x 33)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0201Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0201Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0201Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0201Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 122
  · exact hroot.hOcc 128
  · exact hroot.hOcc 133
  · exact hroot.hOcc 220
  · exact hroot.hOcc 440
  · exact hroot.hOcc 647
  · exact hroot.hOcc 661
  · exact hroot.hOcc 888
  · exact hroot.hOcc 928
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1161
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1203
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1279
  · exact hroot.hOcc 1293
  · exact hroot.hOcc 1300
  · exact hroot.hOcc 1341
  · exact hroot.hOcc 1373
  · exact hroot.hOcc 1375
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1632
  · exact hroot.hOcc 1650
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21
  · change (∑ k, (if k = (31 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (33 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_33

end QiushiMatmul
