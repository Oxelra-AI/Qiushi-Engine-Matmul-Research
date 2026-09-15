import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0442Refs : Fin 44 → RowRef 1665 43 := ![.occ 123, .occ 125, .occ 131, .occ 133, .occ 138, .occ 283, .occ 289, .occ 290, .occ 1190, .occ 1247, .occ 1249, .occ 1250, .occ 1261, .occ 1267, .occ 1275, .occ 1281, .occ 1297, .occ 1298, .occ 1308, .occ 1316, .occ 1335, .occ 1358, .occ 1386, .occ 1393, .occ 1441, .occ 1553, .occ 1602, .occ 1610, .occ 1633, .occ 1658, .occ 1664, .sumGe, .nonneg 23, .nonneg 24, .nonneg 25, .nonneg 26, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 0 (0), .branchLe 29 (0), .branchGe 19 (1), .branchGe 31 (1), .branchLe 30 (0)]

def plane484GenLeaf0442Mult : Fin 44 → Nat := ![29398, 3790, 5450, 154508, 118776, 14743, 13487, 36255, 70, 33650, 12790, 20052, 21725, 20337, 45264, 31601, 5123, 1953, 3411, 11662, 12637, 55615, 58456, 9908, 18713, 10804, 56003, 458, 21635, 17905, 21983, 187156, 153101, 36373, 25877, 34625, 362262, 187156, 112146, 11392, 187156, 361982, 199346, 187086]

theorem plane484GenLeaf0442 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0442Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0442Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0442Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0442Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 123
  · exact hroot.hOcc 125
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 138
  · exact hroot.hOcc 283
  · exact hroot.hOcc 289
  · exact hroot.hOcc 290
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1247
  · exact hroot.hOcc 1249
  · exact hroot.hOcc 1250
  · exact hroot.hOcc 1261
  · exact hroot.hOcc 1267
  · exact hroot.hOcc 1275
  · exact hroot.hOcc 1281
  · exact hroot.hOcc 1297
  · exact hroot.hOcc 1298
  · exact hroot.hOcc 1308
  · exact hroot.hOcc 1316
  · exact hroot.hOcc 1335
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1386
  · exact hroot.hOcc 1393
  · exact hroot.hOcc 1441
  · exact hroot.hOcc 1553
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1633
  · exact hroot.hOcc 1658
  · exact hroot.hOcc 1664
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30

end QiushiMatmul
