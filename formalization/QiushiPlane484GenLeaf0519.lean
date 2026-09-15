import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0519Refs : Fin 44 → RowRef 1665 43 := ![.occ 125, .occ 131, .occ 132, .occ 138, .occ 140, .occ 142, .occ 227, .occ 290, .occ 296, .occ 573, .occ 614, .occ 1159, .occ 1179, .occ 1213, .occ 1242, .occ 1266, .occ 1271, .occ 1276, .occ 1278, .occ 1311, .occ 1340, .occ 1342, .occ 1444, .occ 1447, .occ 1478, .occ 1481, .occ 1571, .occ 1603, .occ 1630, .occ 1633, .occ 1663, .sumGe, .nonneg 20, .nonneg 25, .nonneg 26, .branchGe 15 (1), .branchGe 35 (1), .branchLe 30 (0), .branchGe 34 (1), .branchLe 9 (0), .branchLe 18 (0), .branchLe 3 (0), .branchLe 13 (0), .branchGe 22 (1)]

def plane484GenLeaf0519Mult : Fin 44 → Nat := ![2818, 4148, 9323, 14035, 25740, 25827, 4, 1640, 10778, 1414, 3687, 12648, 1644, 4728, 25042, 13374, 4692, 3888, 14202, 7300, 12220, 6216, 11160, 3398, 16804, 1330, 32004, 5636, 12926, 7968, 2620, 61842, 1174, 466, 78950, 123556, 90712, 61842, 114140, 25920, 16736, 31028, 61842, 174386]

theorem plane484GenLeaf0519 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0519Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0519Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0519Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0519Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 125
  · exact hroot.hOcc 131
  · exact hroot.hOcc 132
  · exact hroot.hOcc 138
  · exact hroot.hOcc 140
  · exact hroot.hOcc 142
  · exact hroot.hOcc 227
  · exact hroot.hOcc 290
  · exact hroot.hOcc 296
  · exact hroot.hOcc 573
  · exact hroot.hOcc 614
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1242
  · exact hroot.hOcc 1266
  · exact hroot.hOcc 1271
  · exact hroot.hOcc 1276
  · exact hroot.hOcc 1278
  · exact hroot.hOcc 1311
  · exact hroot.hOcc 1340
  · exact hroot.hOcc 1342
  · exact hroot.hOcc 1444
  · exact hroot.hOcc 1447
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1630
  · exact hroot.hOcc 1633
  · exact hroot.hOcc 1663
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (9 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22

end QiushiMatmul
