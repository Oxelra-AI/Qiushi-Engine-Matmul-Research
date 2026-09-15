import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0441Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 125, .occ 131, .occ 133, .occ 138, .occ 141, .occ 175, .occ 228, .occ 244, .occ 521, .occ 522, .occ 581, .occ 585, .occ 691, .occ 957, .occ 1043, .occ 1072, .occ 1220, .occ 1270, .occ 1339, .occ 1350, .occ 1361, .occ 1400, .occ 1418, .occ 1423, .occ 1454, .occ 1477, .occ 1489, .occ 1602, .occ 1655, .sumGe, .nonneg 0, .nonneg 2, .nonneg 3, .nonneg 23, .nonneg 24, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 29 (0), .branchGe 19 (1), .branchLe 31 (0), .branchGe 20 (1), .branchGe 9 (1)]

def plane484GenLeaf0441Mult : Fin 44 → Nat := ![1114, 2056, 4140, 3388, 3286, 718, 423, 2126, 2850, 1125, 1606, 156, 1758, 1691, 748, 34, 2516, 510, 68, 834, 34, 777, 36, 2296, 32, 410, 596, 840, 18, 122, 4262, 3438, 1920, 136, 6742, 6838, 15271, 1456, 4262, 4262, 14224, 4244, 14303, 16042]

theorem plane484GenLeaf0441 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0441Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0441Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0441Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0441Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 125
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 138
  · exact hroot.hOcc 141
  · exact hroot.hOcc 175
  · exact hroot.hOcc 228
  · exact hroot.hOcc 244
  · exact hroot.hOcc 521
  · exact hroot.hOcc 522
  · exact hroot.hOcc 581
  · exact hroot.hOcc 585
  · exact hroot.hOcc 691
  · exact hroot.hOcc 957
  · exact hroot.hOcc 1043
  · exact hroot.hOcc 1072
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1270
  · exact hroot.hOcc 1339
  · exact hroot.hOcc 1350
  · exact hroot.hOcc 1361
  · exact hroot.hOcc 1400
  · exact hroot.hOcc 1418
  · exact hroot.hOcc 1423
  · exact hroot.hOcc 1454
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1655
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (31 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20
  · change (∑ k, (if k = (9 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9

end QiushiMatmul
