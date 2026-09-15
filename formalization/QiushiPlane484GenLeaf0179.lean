import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0179Refs : Fin 44 → RowRef 1665 43 := ![.occ 123, .occ 141, .occ 204, .occ 210, .occ 271, .occ 363, .occ 390, .occ 412, .occ 1147, .occ 1159, .occ 1166, .occ 1216, .occ 1220, .occ 1283, .occ 1319, .occ 1327, .occ 1353, .occ 1391, .occ 1398, .occ 1472, .occ 1492, .occ 1499, .occ 1500, .occ 1505, .occ 1571, .occ 1601, .occ 1603, .occ 1606, .occ 1623, .occ 1643, .sumGe, .nonneg 2, .nonneg 12, .nonneg 18, .branchLe 15 (0), .branchGe 29 (1), .branchGe 35 (1), .branchLe 16 (0), .branchLe 1 (0), .branchLe 5 (0), .branchLe 7 (0), .branchLe 14 (0), .branchLe 4 (0), .branchGe 6 (1)]

def plane484GenLeaf0179Mult : Fin 44 → Nat := ![3983, 672, 1111, 5399, 3750, 672, 2486, 6525, 65, 2687, 1517, 435, 448, 457, 168, 1584, 594, 3606, 1463, 56, 6875, 6610, 2240, 2908, 793, 1349, 233, 47, 5647, 2482, 13629, 569, 625, 5314, 10942, 35997, 31870, 6876, 13573, 5239, 5672, 6633, 13629, 44435]

theorem plane484GenLeaf0179 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0179Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0179Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0179Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0179Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 123
  · exact hroot.hOcc 141
  · exact hroot.hOcc 204
  · exact hroot.hOcc 210
  · exact hroot.hOcc 271
  · exact hroot.hOcc 363
  · exact hroot.hOcc 390
  · exact hroot.hOcc 412
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1283
  · exact hroot.hOcc 1319
  · exact hroot.hOcc 1327
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1391
  · exact hroot.hOcc 1398
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1499
  · exact hroot.hOcc 1500
  · exact hroot.hOcc 1505
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1623
  · exact hroot.hOcc 1643
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (12 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6

end QiushiMatmul
