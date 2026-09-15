import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0130Refs : Fin 43 → RowRef 1665 43 := ![.occ 122, .occ 128, .occ 129, .occ 130, .occ 134, .occ 139, .occ 153, .occ 174, .occ 178, .occ 193, .occ 348, .occ 351, .occ 401, .occ 659, .occ 985, .occ 1009, .occ 1146, .occ 1160, .occ 1215, .occ 1256, .occ 1323, .occ 1383, .occ 1395, .occ 1403, .occ 1478, .occ 1491, .occ 1501, .occ 1503, .occ 1610, .occ 1625, .occ 1652, .sumGe, .nonneg 21, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 39 (0), .branchLe 32 (0), .branchGe 28 (1), .branchGe 6 (1), .branchGe 33 (1)]

def plane484GenLeaf0130Mult : Fin 43 → Nat := ![5, 7, 202, 7, 14, 10, 3, 104, 192, 20, 12, 70, 93, 45, 28, 27, 92, 18, 16, 2, 86, 18, 70, 36, 180, 4, 94, 134, 12, 81, 88, 320, 6, 232, 224, 54, 122, 32, 147, 234, 898, 983, 1112]

theorem plane484GenLeaf0130 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_33 : (1 : Int) ≤ x 33)
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0130Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0130Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0130Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0130Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 122
  · exact hroot.hOcc 128
  · exact hroot.hOcc 129
  · exact hroot.hOcc 130
  · exact hroot.hOcc 134
  · exact hroot.hOcc 139
  · exact hroot.hOcc 153
  · exact hroot.hOcc 174
  · exact hroot.hOcc 178
  · exact hroot.hOcc 193
  · exact hroot.hOcc 348
  · exact hroot.hOcc 351
  · exact hroot.hOcc 401
  · exact hroot.hOcc 659
  · exact hroot.hOcc 985
  · exact hroot.hOcc 1009
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1256
  · exact hroot.hOcc 1323
  · exact hroot.hOcc 1383
  · exact hroot.hOcc 1395
  · exact hroot.hOcc 1403
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1501
  · exact hroot.hOcc 1503
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1625
  · exact hroot.hOcc 1652
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (33 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_33

end QiushiMatmul
