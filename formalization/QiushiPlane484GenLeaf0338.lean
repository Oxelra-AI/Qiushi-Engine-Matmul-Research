import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0338Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 122, .occ 125, .occ 126, .occ 136, .occ 139, .occ 140, .occ 141, .occ 144, .occ 222, .occ 243, .occ 408, .occ 535, .occ 717, .occ 753, .occ 816, .occ 1187, .occ 1190, .occ 1196, .occ 1220, .occ 1353, .occ 1367, .occ 1455, .occ 1458, .occ 1573, .occ 1580, .occ 1600, .occ 1603, .occ 1608, .sumGe, .nonneg 7, .nonneg 8, .nonneg 13, .branchLe 15 (0), .branchGe 2 (1), .branchLe 23 (0), .branchGe 26 (1), .branchGe 1 (1), .branchGe 30 (1), .branchGe 36 (1), .branchLe 18 (0), .branchLe 6 (0), .branchLe 29 (0), .branchGe 11 (1)]

def plane484GenLeaf0338Mult : Fin 44 → Nat := ![29, 25, 72, 63, 24, 63, 48, 6, 55, 84, 103, 10, 54, 15, 29, 117, 18, 57, 59, 24, 24, 2, 3, 34, 18, 12, 10, 1, 53, 147, 112, 53, 24, 99, 164, 95, 347, 90, 359, 326, 68, 59, 122, 455]

theorem plane484GenLeaf0338 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0338Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0338Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0338Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0338Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 122
  · exact hroot.hOcc 125
  · exact hroot.hOcc 126
  · exact hroot.hOcc 136
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 141
  · exact hroot.hOcc 144
  · exact hroot.hOcc 222
  · exact hroot.hOcc 243
  · exact hroot.hOcc 408
  · exact hroot.hOcc 535
  · exact hroot.hOcc 717
  · exact hroot.hOcc 753
  · exact hroot.hOcc 816
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1367
  · exact hroot.hOcc 1455
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1600
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1608
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (36 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11

end QiushiMatmul
