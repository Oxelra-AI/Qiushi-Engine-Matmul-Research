import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0323Refs : Fin 43 → RowRef 1665 43 := ![.occ 100, .occ 122, .occ 123, .occ 124, .occ 125, .occ 128, .occ 138, .occ 139, .occ 141, .occ 142, .occ 340, .occ 1128, .occ 1147, .occ 1168, .occ 1186, .occ 1187, .occ 1214, .occ 1242, .occ 1250, .occ 1320, .occ 1393, .occ 1416, .occ 1440, .occ 1462, .occ 1489, .occ 1495, .occ 1496, .occ 1625, .sumGe, .nonneg 19, .nonneg 24, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchGe 26 (1), .branchLe 14 (0), .branchGe 1 (1), .branchLe 30 (0), .branchLe 17 (0), .branchLe 38 (0), .branchLe 16 (0), .branchLe 20 (0)]

def plane484GenLeaf0323Mult : Fin 43 → Nat := ![570, 5529, 1791, 966, 2073, 4395, 1190, 9620, 3656, 8590, 4362, 822, 6330, 3450, 2616, 834, 7236, 858, 336, 1668, 1932, 384, 1020, 6498, 834, 114, 8262, 2526, 19044, 1782, 4310, 5118, 5966, 18078, 1594, 48028, 6078, 14234, 18210, 12862, 12594, 834, 12028]

theorem plane484GenLeaf0323 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0323Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0323Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0323Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0323Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 100
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 125
  · exact hroot.hOcc 128
  · exact hroot.hOcc 138
  · exact hroot.hOcc 139
  · exact hroot.hOcc 141
  · exact hroot.hOcc 142
  · exact hroot.hOcc 340
  · exact hroot.hOcc 1128
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1242
  · exact hroot.hOcc 1250
  · exact hroot.hOcc 1320
  · exact hroot.hOcc 1393
  · exact hroot.hOcc 1416
  · exact hroot.hOcc 1440
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1495
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1625
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (38 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20

end QiushiMatmul
