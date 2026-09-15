import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0389Refs : Fin 39 → RowRef 1665 43 := ![.occ 123, .occ 125, .occ 131, .occ 132, .occ 137, .occ 138, .occ 616, .occ 1146, .occ 1147, .occ 1159, .occ 1160, .occ 1213, .occ 1458, .occ 1472, .occ 1478, .occ 1481, .occ 1483, .occ 1484, .occ 1488, .occ 1492, .occ 1495, .occ 1496, .occ 1573, .occ 1638, .sumGe, .nonneg 15, .nonneg 18, .nonneg 24, .nonneg 25, .nonneg 26, .branchGe 2 (1), .branchLe 7 (0), .branchGe 23 (1), .branchGe 35 (1), .branchGe 30 (1), .branchGe 42 (1), .branchGe 39 (1), .branchLe 37 (0), .branchLe 10 (0)]

def plane484GenLeaf0389Mult : Fin 39 → Nat := ![12, 32, 31, 31, 25, 29, 26, 20, 8, 8, 8, 32, 32, 7, 7, 3, 1, 25, 15, 15, 8, 4, 16, 11, 78, 16, 16, 10, 12, 24, 146, 78, 176, 100, 30, 50, 24, 70, 78]

theorem plane484GenLeaf0389 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0389Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0389Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0389Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0389Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 123
  · exact hroot.hOcc 125
  · exact hroot.hOcc 131
  · exact hroot.hOcc 132
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 616
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1495
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1638
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (39 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (37 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10

end QiushiMatmul
