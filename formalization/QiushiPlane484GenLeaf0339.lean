import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0339Refs : Fin 44 → RowRef 1665 43 := ![.occ 124, .occ 137, .occ 139, .occ 140, .occ 141, .occ 206, .occ 222, .occ 238, .occ 325, .occ 366, .occ 582, .occ 592, .occ 808, .occ 837, .occ 855, .occ 1100, .occ 1101, .occ 1154, .occ 1187, .occ 1191, .occ 1214, .occ 1215, .occ 1216, .occ 1353, .occ 1455, .occ 1472, .occ 1477, .occ 1496, .occ 1538, .occ 1607, .sumGe, .nonneg 21, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchGe 26 (1), .branchLe 14 (0), .branchGe 1 (1), .branchGe 30 (1), .branchGe 36 (1), .branchLe 18 (0), .branchLe 6 (0), .branchGe 29 (1)]

def plane484GenLeaf0339Mult : Fin 44 → Nat := ![492, 610, 371, 377, 37, 768, 636, 508, 40, 55, 236, 16, 204, 352, 116, 16, 28, 156, 484, 192, 184, 320, 724, 44, 24, 284, 72, 292, 36, 376, 1252, 112, 780, 858, 340, 310, 3058, 1252, 540, 2212, 3048, 804, 1180, 1772]

theorem plane484GenLeaf0339 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0339Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0339Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0339Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0339Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 124
  · exact hroot.hOcc 137
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 141
  · exact hroot.hOcc 206
  · exact hroot.hOcc 222
  · exact hroot.hOcc 238
  · exact hroot.hOcc 325
  · exact hroot.hOcc 366
  · exact hroot.hOcc 582
  · exact hroot.hOcc 592
  · exact hroot.hOcc 808
  · exact hroot.hOcc 837
  · exact hroot.hOcc 855
  · exact hroot.hOcc 1100
  · exact hroot.hOcc 1101
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1455
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1538
  · exact hroot.hOcc 1607
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (36 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29

end QiushiMatmul
