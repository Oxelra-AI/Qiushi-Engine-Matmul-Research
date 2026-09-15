import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0463Refs : Fin 43 → RowRef 1665 43 := ![.occ 122, .occ 135, .occ 136, .occ 137, .occ 138, .occ 139, .occ 174, .occ 191, .occ 194, .occ 366, .occ 396, .occ 640, .occ 654, .occ 814, .occ 856, .occ 865, .occ 867, .occ 1082, .occ 1103, .occ 1188, .occ 1283, .occ 1296, .occ 1315, .occ 1358, .occ 1403, .occ 1442, .occ 1544, .occ 1550, .occ 1567, .occ 1590, .occ 1619, .occ 1653, .sumGe, .nonneg 0, .nonneg 7, .branchGe 15 (1), .branchLe 35 (0), .branchGe 29 (1), .branchGe 27 (1), .branchLe 8 (0), .branchGe 4 (1), .branchLe 5 (0), .branchGe 16 (1)]

def plane484GenLeaf0463Mult : Fin 43 → Nat := ![204, 137, 379, 181, 137, 510, 10, 546, 118, 162, 250, 100, 194, 844, 908, 694, 298, 72, 364, 124, 102, 102, 148, 662, 46, 386, 184, 112, 318, 194, 102, 368, 1276, 14, 194, 1814, 1276, 2196, 3764, 590, 4336, 1276, 5354]

theorem plane484GenLeaf0463 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0463Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0463Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0463Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0463Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 122
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 139
  · exact hroot.hOcc 174
  · exact hroot.hOcc 191
  · exact hroot.hOcc 194
  · exact hroot.hOcc 366
  · exact hroot.hOcc 396
  · exact hroot.hOcc 640
  · exact hroot.hOcc 654
  · exact hroot.hOcc 814
  · exact hroot.hOcc 856
  · exact hroot.hOcc 865
  · exact hroot.hOcc 867
  · exact hroot.hOcc 1082
  · exact hroot.hOcc 1103
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1283
  · exact hroot.hOcc 1296
  · exact hroot.hOcc 1315
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1403
  · exact hroot.hOcc 1442
  · exact hroot.hOcc 1544
  · exact hroot.hOcc 1550
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1619
  · exact hroot.hOcc 1653
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (27 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16

end QiushiMatmul
