import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0425Refs : Fin 43 → RowRef 1665 43 := ![.occ 119, .occ 121, .occ 126, .occ 136, .occ 139, .occ 156, .occ 213, .occ 233, .occ 245, .occ 279, .occ 280, .occ 328, .occ 396, .occ 582, .occ 634, .occ 708, .occ 716, .occ 841, .occ 1166, .occ 1174, .occ 1179, .occ 1183, .occ 1196, .occ 1294, .occ 1325, .occ 1491, .occ 1496, .occ 1508, .occ 1512, .occ 1549, .occ 1571, .occ 1588, .occ 1603, .occ 1657, .sumGe, .nonneg 5, .branchLe 15 (0), .branchGe 2 (1), .branchGe 7 (1), .branchLe 6 (0), .branchGe 31 (1), .branchGe 29 (1), .branchGe 36 (1)]

def plane484GenLeaf0425Mult : Fin 43 → Nat := ![175, 177, 47, 211, 10, 20, 29, 58, 149, 345, 49, 96, 47, 124, 347, 242, 359, 20, 121, 39, 139, 278, 141, 207, 80, 20, 159, 29, 21, 17, 92, 54, 20, 139, 558, 159, 558, 390, 2149, 119, 1608, 984, 2119]

theorem plane484GenLeaf0425 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0425Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0425Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0425Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0425Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 126
  · exact hroot.hOcc 136
  · exact hroot.hOcc 139
  · exact hroot.hOcc 156
  · exact hroot.hOcc 213
  · exact hroot.hOcc 233
  · exact hroot.hOcc 245
  · exact hroot.hOcc 279
  · exact hroot.hOcc 280
  · exact hroot.hOcc 328
  · exact hroot.hOcc 396
  · exact hroot.hOcc 582
  · exact hroot.hOcc 634
  · exact hroot.hOcc 708
  · exact hroot.hOcc 716
  · exact hroot.hOcc 841
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1294
  · exact hroot.hOcc 1325
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1508
  · exact hroot.hOcc 1512
  · exact hroot.hOcc 1549
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1588
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1657
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (36 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36

end QiushiMatmul
