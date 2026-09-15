import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0380Refs : Fin 44 → RowRef 1665 43 := ![.occ 121, .occ 123, .occ 125, .occ 130, .occ 131, .occ 132, .occ 134, .occ 137, .occ 754, .occ 793, .occ 800, .occ 1145, .occ 1146, .occ 1147, .occ 1164, .occ 1172, .occ 1179, .occ 1191, .occ 1213, .occ 1383, .occ 1426, .occ 1434, .occ 1458, .occ 1459, .occ 1478, .occ 1481, .occ 1484, .occ 1488, .occ 1492, .occ 1495, .occ 1496, .occ 1606, .occ 1609, .sumGe, .nonneg 26, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchGe 23 (1), .branchGe 35 (1), .branchLe 30 (0), .branchGe 42 (1), .branchLe 19 (0), .branchLe 10 (0)]

def plane484GenLeaf0380Mult : Fin 44 → Nat := ![7620, 30157, 62242, 7472, 8390, 83892, 41896, 53145, 36073, 6352, 34103, 9530, 34359, 26115, 15346, 14669, 7170, 15902, 44714, 8021, 8725, 24955, 46630, 448, 14595, 10060, 29190, 11367, 12685, 10985, 69234, 33230, 74, 163073, 19780, 125493, 211898, 140107, 379270, 118352, 103310, 193654, 154683, 113646]

theorem plane484GenLeaf0380 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0380Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0380Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0380Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0380Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 123
  · exact hroot.hOcc 125
  · exact hroot.hOcc 130
  · exact hroot.hOcc 131
  · exact hroot.hOcc 132
  · exact hroot.hOcc 134
  · exact hroot.hOcc 137
  · exact hroot.hOcc 754
  · exact hroot.hOcc 793
  · exact hroot.hOcc 800
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1383
  · exact hroot.hOcc 1426
  · exact hroot.hOcc 1434
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1495
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1609
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10

end QiushiMatmul
