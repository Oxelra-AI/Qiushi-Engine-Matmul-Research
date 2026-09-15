import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0167Refs : Fin 41 → RowRef 1665 43 := ![.occ 121, .occ 126, .occ 127, .occ 129, .occ 161, .occ 174, .occ 271, .occ 272, .occ 412, .occ 497, .occ 663, .occ 780, .occ 1009, .occ 1151, .occ 1166, .occ 1216, .occ 1232, .occ 1271, .occ 1273, .occ 1276, .occ 1296, .occ 1323, .occ 1337, .occ 1403, .occ 1408, .occ 1427, .occ 1491, .occ 1501, .occ 1545, .sumGe, .nonneg 14, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchGe 7 (1), .branchLe 18 (0), .branchGe 30 (1), .branchLe 20 (0), .branchGe 33 (1), .branchGe 6 (1)]

def plane484GenLeaf0167Mult : Fin 41 → Nat := ![12, 8, 23, 34, 13, 21, 7, 6, 14, 8, 11, 12, 9, 11, 8, 4, 8, 18, 2, 4, 6, 13, 3, 12, 4, 4, 14, 14, 6, 46, 64, 24, 24, 80, 46, 113, 36, 64, 44, 106, 171]

theorem plane484GenLeaf0167 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_33 : (1 : Int) ≤ x 33)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0167Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0167Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0167Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0167Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 126
  · exact hroot.hOcc 127
  · exact hroot.hOcc 129
  · exact hroot.hOcc 161
  · exact hroot.hOcc 174
  · exact hroot.hOcc 271
  · exact hroot.hOcc 272
  · exact hroot.hOcc 412
  · exact hroot.hOcc 497
  · exact hroot.hOcc 663
  · exact hroot.hOcc 780
  · exact hroot.hOcc 1009
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1232
  · exact hroot.hOcc 1271
  · exact hroot.hOcc 1273
  · exact hroot.hOcc 1276
  · exact hroot.hOcc 1296
  · exact hroot.hOcc 1323
  · exact hroot.hOcc 1337
  · exact hroot.hOcc 1403
  · exact hroot.hOcc 1408
  · exact hroot.hOcc 1427
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1501
  · exact hroot.hOcc 1545
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (33 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_33
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6

end QiushiMatmul
