import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0356Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 124, .occ 125, .occ 126, .occ 131, .occ 133, .occ 137, .occ 138, .occ 246, .occ 272, .occ 361, .occ 541, .occ 773, .occ 831, .occ 1047, .occ 1145, .occ 1151, .occ 1170, .occ 1179, .occ 1187, .occ 1190, .occ 1191, .occ 1390, .occ 1401, .occ 1459, .occ 1486, .occ 1489, .occ 1601, .occ 1629, .occ 1633, .occ 1639, .sumGe, .nonneg 15, .nonneg 20, .nonneg 22, .branchGe 2 (1), .branchLe 7 (0), .branchGe 23 (1), .branchLe 35 (0), .branchLe 3 (0), .branchLe 24 (0), .branchLe 18 (0), .branchGe 19 (1), .branchLe 28 (0)]

def plane484GenLeaf0356Mult : Fin 44 → Nat := ![1602, 3674, 7249, 1058, 9544, 6532, 1467, 14977, 854, 5694, 1158, 802, 593, 3424, 418, 2145, 3909, 1776, 960, 5718, 1276, 4690, 705, 1059, 3282, 2322, 1703, 4068, 2307, 533, 13, 16990, 17962, 1581, 6560, 29835, 9403, 30132, 11932, 13092, 5301, 1480, 40837, 16990]

theorem plane484GenLeaf0356 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0356Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0356Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0356Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0356Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 124
  · exact hroot.hOcc 125
  · exact hroot.hOcc 126
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 246
  · exact hroot.hOcc 272
  · exact hroot.hOcc 361
  · exact hroot.hOcc 541
  · exact hroot.hOcc 773
  · exact hroot.hOcc 831
  · exact hroot.hOcc 1047
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1390
  · exact hroot.hOcc 1401
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1629
  · exact hroot.hOcc 1633
  · exact hroot.hOcc 1639
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28

end QiushiMatmul
