import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0321Refs : Fin 43 → RowRef 1665 43 := ![.occ 123, .occ 124, .occ 137, .occ 138, .occ 614, .occ 1143, .occ 1145, .occ 1146, .occ 1147, .occ 1187, .occ 1196, .occ 1215, .occ 1250, .occ 1266, .occ 1282, .occ 1297, .occ 1303, .occ 1328, .occ 1398, .occ 1403, .occ 1432, .occ 1440, .occ 1486, .occ 1488, .occ 1489, .occ 1492, .occ 1502, .occ 1520, .occ 1544, .occ 1563, .occ 1573, .occ 1603, .sumGe, .nonneg 15, .nonneg 19, .nonneg 23, .branchGe 2 (1), .branchLe 7 (0), .branchGe 26 (1), .branchLe 14 (0), .branchLe 1 (0), .branchGe 22 (1), .branchLe 0 (0)]

def plane484GenLeaf0321Mult : Fin 43 → Nat := ![51, 25, 70, 136, 46, 24, 21, 8, 12, 10, 19, 20, 11, 15, 17, 7, 9, 2, 9, 1, 20, 22, 12, 24, 3, 25, 11, 33, 8, 11, 18, 20, 136, 136, 68, 108, 368, 80, 284, 136, 116, 244, 116]

theorem plane484GenLeaf0321 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0321Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0321Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0321Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0321Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 614
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1250
  · exact hroot.hOcc 1266
  · exact hroot.hOcc 1282
  · exact hroot.hOcc 1297
  · exact hroot.hOcc 1303
  · exact hroot.hOcc 1328
  · exact hroot.hOcc 1398
  · exact hroot.hOcc 1403
  · exact hroot.hOcc 1432
  · exact hroot.hOcc 1440
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1502
  · exact hroot.hOcc 1520
  · exact hroot.hOcc 1544
  · exact hroot.hOcc 1563
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1603
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0

end QiushiMatmul
