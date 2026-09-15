import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0381Refs : Fin 44 → RowRef 1665 43 := ![.occ 124, .occ 126, .occ 128, .occ 132, .occ 134, .occ 319, .occ 386, .occ 773, .occ 774, .occ 787, .occ 789, .occ 793, .occ 1047, .occ 1051, .occ 1147, .occ 1159, .occ 1168, .occ 1179, .occ 1206, .occ 1213, .occ 1282, .occ 1438, .occ 1458, .occ 1459, .occ 1470, .occ 1481, .occ 1484, .occ 1488, .occ 1492, .occ 1496, .occ 1552, .occ 1606, .sumGe, .nonneg 4, .nonneg 6, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchGe 23 (1), .branchGe 35 (1), .branchLe 30 (0), .branchGe 42 (1), .branchLe 19 (0), .branchGe 10 (1)]

def plane484GenLeaf0381Mult : Fin 44 → Nat := ![7297, 4077, 5720, 3319, 4916, 1562, 8688, 4214, 1890, 6107, 166, 619, 9004, 1057, 2412, 415, 3117, 3565, 1520, 165, 848, 8255, 166, 1029, 257, 2214, 591, 3734, 3532, 3121, 540, 10487, 17338, 1335, 2950, 14812, 18328, 5964, 45328, 20622, 12611, 39105, 17338, 40945]

theorem plane484GenLeaf0381 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0381Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0381Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0381Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0381Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 124
  · exact hroot.hOcc 126
  · exact hroot.hOcc 128
  · exact hroot.hOcc 132
  · exact hroot.hOcc 134
  · exact hroot.hOcc 319
  · exact hroot.hOcc 386
  · exact hroot.hOcc 773
  · exact hroot.hOcc 774
  · exact hroot.hOcc 787
  · exact hroot.hOcc 789
  · exact hroot.hOcc 793
  · exact hroot.hOcc 1047
  · exact hroot.hOcc 1051
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1282
  · exact hroot.hOcc 1438
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1552
  · exact hroot.hOcc 1606
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
