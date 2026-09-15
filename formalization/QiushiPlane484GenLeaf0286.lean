import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0286Refs : Fin 43 → RowRef 1665 43 := ![.occ 121, .occ 124, .occ 129, .occ 135, .occ 136, .occ 137, .occ 548, .occ 549, .occ 737, .occ 824, .occ 850, .occ 1154, .occ 1170, .occ 1186, .occ 1190, .occ 1257, .occ 1259, .occ 1268, .occ 1269, .occ 1315, .occ 1472, .occ 1481, .occ 1484, .occ 1492, .occ 1529, .occ 1533, .occ 1610, .occ 1643, .sumGe, .nonneg 3, .nonneg 7, .nonneg 12, .nonneg 17, .branchLe 15 (0), .branchGe 2 (1), .branchLe 23 (0), .branchLe 26 (0), .branchGe 29 (1), .branchLe 34 (0), .branchGe 13 (1), .branchLe 24 (0), .branchLe 22 (0), .branchGe 5 (1)]

def plane484GenLeaf0286Mult : Fin 43 → Nat := ![979, 1720, 1576, 582, 88, 148, 45, 45, 556, 26, 2, 324, 36, 143, 685, 475, 567, 128, 433, 36, 417, 144, 460, 35, 570, 15, 108, 1, 1720, 72, 4182, 1182, 454, 678, 2286, 968, 1571, 1432, 1720, 6036, 409, 1150, 5594]

theorem plane484GenLeaf0286 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0286Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0286Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0286Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0286Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 124
  · exact hroot.hOcc 129
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 548
  · exact hroot.hOcc 549
  · exact hroot.hOcc 737
  · exact hroot.hOcc 824
  · exact hroot.hOcc 850
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1257
  · exact hroot.hOcc 1259
  · exact hroot.hOcc 1268
  · exact hroot.hOcc 1269
  · exact hroot.hOcc 1315
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1529
  · exact hroot.hOcc 1533
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1643
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (12 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5

end QiushiMatmul
