import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0281Refs : Fin 44 → RowRef 1665 43 := ![.occ 123, .occ 136, .occ 139, .occ 141, .occ 180, .occ 363, .occ 405, .occ 551, .occ 1140, .occ 1148, .occ 1151, .occ 1153, .occ 1154, .occ 1155, .occ 1170, .occ 1180, .occ 1187, .occ 1261, .occ 1269, .occ 1315, .occ 1433, .occ 1481, .occ 1486, .occ 1489, .occ 1492, .occ 1603, .occ 1609, .occ 1618, .sumGe, .nonneg 22, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchGe 29 (1), .branchLe 34 (0), .branchLe 13 (0), .branchGe 37 (1), .branchGe 32 (1), .branchLe 10 (0), .branchLe 4 (0), .branchLe 14 (0), .branchGe 19 (1)]

def plane484GenLeaf0281Mult : Fin 44 → Nat := ![984, 66, 463, 1319, 346, 1482, 266, 282, 542, 1254, 597, 312, 137, 326, 1312, 396, 928, 435, 1251, 114, 617, 4, 2029, 8, 286, 405, 282, 313, 3631, 872, 3631, 1416, 1289, 3631, 282, 3924, 3623, 2533, 2407, 6099, 1602, 2375, 2846, 9583]

theorem plane484GenLeaf0281 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0281Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0281Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0281Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0281Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 123
  · exact hroot.hOcc 136
  · exact hroot.hOcc 139
  · exact hroot.hOcc 141
  · exact hroot.hOcc 180
  · exact hroot.hOcc 363
  · exact hroot.hOcc 405
  · exact hroot.hOcc 551
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1148
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1153
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1155
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1180
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1261
  · exact hroot.hOcc 1269
  · exact hroot.hOcc 1315
  · exact hroot.hOcc 1433
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1618
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37
  · change (∑ k, (if k = (32 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19

end QiushiMatmul
