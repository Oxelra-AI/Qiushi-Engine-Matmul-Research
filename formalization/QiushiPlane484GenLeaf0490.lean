import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0490Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 120, .occ 130, .occ 131, .occ 133, .occ 138, .occ 171, .occ 498, .occ 596, .occ 861, .occ 1136, .occ 1140, .occ 1145, .occ 1150, .occ 1159, .occ 1168, .occ 1170, .occ 1187, .occ 1200, .occ 1205, .occ 1220, .occ 1340, .occ 1371, .occ 1401, .occ 1427, .occ 1459, .occ 1522, .occ 1601, .occ 1609, .occ 1619, .occ 1629, .occ 1646, .occ 1659, .sumGe, .nonneg 18, .nonneg 20, .nonneg 23, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchGe 0 (1), .branchGe 19 (1), .branchLe 28 (0), .branchGe 30 (1)]

def plane484GenLeaf0490Mult : Fin 44 → Nat := ![1624, 1893, 2003, 8316, 5040, 7504, 2052, 172, 2170, 942, 1118, 396, 371, 2629, 24, 947, 653, 1561, 372, 24, 3179, 193, 502, 1025, 606, 705, 1010, 3603, 2948, 2555, 1506, 1434, 347, 11242, 3144, 7460, 15818, 21822, 7362, 9618, 17968, 28354, 11242, 10604]

theorem plane484GenLeaf0490 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0490Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0490Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0490Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0490Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 120
  · exact hroot.hOcc 130
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 138
  · exact hroot.hOcc 171
  · exact hroot.hOcc 498
  · exact hroot.hOcc 596
  · exact hroot.hOcc 861
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1340
  · exact hroot.hOcc 1371
  · exact hroot.hOcc 1401
  · exact hroot.hOcc 1427
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1522
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1619
  · exact hroot.hOcc 1629
  · exact hroot.hOcc 1646
  · exact hroot.hOcc 1659
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30

end QiushiMatmul
