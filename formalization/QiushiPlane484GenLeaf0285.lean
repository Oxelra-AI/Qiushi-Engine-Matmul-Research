import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0285Refs : Fin 44 → RowRef 1665 43 := ![.occ 122, .occ 123, .occ 130, .occ 135, .occ 137, .occ 139, .occ 214, .occ 277, .occ 458, .occ 630, .occ 707, .occ 1151, .occ 1172, .occ 1183, .occ 1190, .occ 1220, .occ 1358, .occ 1417, .occ 1458, .occ 1459, .occ 1471, .occ 1481, .occ 1483, .occ 1484, .occ 1488, .occ 1567, .occ 1602, .occ 1620, .occ 1643, .occ 1649, .sumGe, .nonneg 3, .nonneg 12, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchGe 29 (1), .branchLe 34 (0), .branchGe 13 (1), .branchLe 24 (0), .branchLe 22 (0), .branchLe 5 (0)]

def plane484GenLeaf0285Mult : Fin 44 → Nat := ![16498, 18511, 9002, 4560, 130, 6744, 13141, 1091, 4764, 2679, 5925, 3656, 11671, 5673, 18050, 1229, 2868, 3809, 11323, 3728, 851, 5011, 5894, 8050, 2805, 5011, 7567, 10776, 4135, 6238, 49038, 63, 6831, 23857, 28792, 43365, 23484, 21328, 3669, 38666, 107889, 37734, 31129, 49038]

theorem plane484GenLeaf0285 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0285Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0285Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0285Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0285Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 130
  · exact hroot.hOcc 135
  · exact hroot.hOcc 137
  · exact hroot.hOcc 139
  · exact hroot.hOcc 214
  · exact hroot.hOcc 277
  · exact hroot.hOcc 458
  · exact hroot.hOcc 630
  · exact hroot.hOcc 707
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1417
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1620
  · exact hroot.hOcc 1643
  · exact hroot.hOcc 1649
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (12 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5

end QiushiMatmul
