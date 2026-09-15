import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0260Refs : Fin 42 → RowRef 1665 43 := ![.occ 121, .occ 123, .occ 126, .occ 128, .occ 136, .occ 269, .occ 433, .occ 485, .occ 694, .occ 1136, .occ 1150, .occ 1160, .occ 1190, .occ 1205, .occ 1245, .occ 1246, .occ 1308, .occ 1314, .occ 1322, .occ 1371, .occ 1413, .occ 1435, .occ 1472, .occ 1552, .occ 1567, .occ 1609, .occ 1610, .occ 1614, .occ 1663, .sumGe, .nonneg 13, .nonneg 16, .nonneg 19, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchLe 29 (0), .branchGe 17 (1), .branchGe 3 (1), .branchLe 20 (0)]

def plane484GenLeaf0260Mult : Fin 42 → Nat := ![297, 443, 279, 185, 830, 150, 264, 128, 44, 186, 44, 279, 193, 127, 28, 38, 9, 149, 50, 9, 129, 52, 275, 136, 179, 147, 15, 203, 98, 928, 236, 274, 310, 792, 996, 254, 328, 928, 284, 2312, 2248, 928]

theorem plane484GenLeaf0260 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0260Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0260Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0260Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0260Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 123
  · exact hroot.hOcc 126
  · exact hroot.hOcc 128
  · exact hroot.hOcc 136
  · exact hroot.hOcc 269
  · exact hroot.hOcc 433
  · exact hroot.hOcc 485
  · exact hroot.hOcc 694
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1245
  · exact hroot.hOcc 1246
  · exact hroot.hOcc 1308
  · exact hroot.hOcc 1314
  · exact hroot.hOcc 1322
  · exact hroot.hOcc 1371
  · exact hroot.hOcc 1413
  · exact hroot.hOcc 1435
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1552
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1614
  · exact hroot.hOcc 1663
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20

end QiushiMatmul
