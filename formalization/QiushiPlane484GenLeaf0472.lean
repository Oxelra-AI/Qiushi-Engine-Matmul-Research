import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0472Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 123, .occ 125, .occ 127, .occ 132, .occ 135, .occ 138, .occ 142, .occ 581, .occ 654, .occ 1100, .occ 1104, .occ 1107, .occ 1136, .occ 1146, .occ 1158, .occ 1166, .occ 1172, .occ 1188, .occ 1200, .occ 1205, .occ 1206, .occ 1385, .occ 1432, .occ 1453, .occ 1462, .occ 1467, .occ 1469, .occ 1615, .occ 1626, .occ 1629, .sumGe, .nonneg 11, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchGe 0 (1), .branchLe 19 (0), .branchLe 25 (0), .branchLe 3 (0), .branchLe 38 (0), .branchLe 20 (0), .branchGe 27 (1), .branchLe 13 (0)]

def plane484GenLeaf0472Mult : Fin 44 → Nat := ![5329, 1, 478, 843, 429, 2097, 1997, 4034, 1776, 1913, 255, 632, 538, 769, 1299, 1440, 4307, 1225, 950, 2764, 975, 754, 247, 37, 46, 935, 1723, 974, 4650, 580, 1512, 10124, 816, 18935, 6955, 2364, 12894, 6615, 2234, 1601, 7600, 6251, 8601, 8898]

theorem plane484GenLeaf0472 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0472Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0472Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0472Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0472Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 123
  · exact hroot.hOcc 125
  · exact hroot.hOcc 127
  · exact hroot.hOcc 132
  · exact hroot.hOcc 135
  · exact hroot.hOcc 138
  · exact hroot.hOcc 142
  · exact hroot.hOcc 581
  · exact hroot.hOcc 654
  · exact hroot.hOcc 1100
  · exact hroot.hOcc 1104
  · exact hroot.hOcc 1107
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1385
  · exact hroot.hOcc 1432
  · exact hroot.hOcc 1453
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1469
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1626
  · exact hroot.hOcc 1629
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (38 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (27 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13

end QiushiMatmul
