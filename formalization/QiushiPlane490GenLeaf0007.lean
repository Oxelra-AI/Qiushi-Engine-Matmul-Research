import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0007Refs : Fin 44 → RowRef 713 43 := ![.occ 84, .occ 87, .occ 91, .occ 100, .occ 104, .occ 107, .occ 110, .occ 112, .occ 134, .occ 150, .occ 153, .occ 208, .occ 210, .occ 234, .occ 235, .occ 238, .occ 245, .occ 249, .occ 252, .occ 282, .occ 284, .occ 291, .occ 303, .occ 314, .occ 335, .occ 364, .occ 380, .occ 405, .occ 447, .occ 452, .occ 457, .occ 522, .occ 560, .occ 668, .occ 671, .sumGe, .nonneg 38, .branchLe 29 (0), .branchLe 4 (0), .branchLe 23 (0), .branchLe 16 (0), .branchLe 39 (0), .branchGe 19 (1), .branchGe 30 (1)]

def plane490GenLeaf0007Mult : Fin 44 → Nat := ![278, 65, 733, 1164, 1129, 1252, 1513, 1575, 901, 710, 1258, 656, 1029, 407, 411, 426, 848, 2883, 2925, 175, 486, 1680, 1179, 733, 918, 2130, 732, 467, 1087, 601, 426, 1129, 542, 678, 411, 4438, 2830, 4027, 2172, 3760, 4438, 4438, 8138, 10747]

theorem plane490GenLeaf0007 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0007Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0007Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0007Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0007Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 84
  · exact hroot.hOcc 87
  · exact hroot.hOcc 91
  · exact hroot.hOcc 100
  · exact hroot.hOcc 104
  · exact hroot.hOcc 107
  · exact hroot.hOcc 110
  · exact hroot.hOcc 112
  · exact hroot.hOcc 134
  · exact hroot.hOcc 150
  · exact hroot.hOcc 153
  · exact hroot.hOcc 208
  · exact hroot.hOcc 210
  · exact hroot.hOcc 234
  · exact hroot.hOcc 235
  · exact hroot.hOcc 238
  · exact hroot.hOcc 245
  · exact hroot.hOcc 249
  · exact hroot.hOcc 252
  · exact hroot.hOcc 282
  · exact hroot.hOcc 284
  · exact hroot.hOcc 291
  · exact hroot.hOcc 303
  · exact hroot.hOcc 314
  · exact hroot.hOcc 335
  · exact hroot.hOcc 364
  · exact hroot.hOcc 380
  · exact hroot.hOcc 405
  · exact hroot.hOcc 447
  · exact hroot.hOcc 452
  · exact hroot.hOcc 457
  · exact hroot.hOcc 522
  · exact hroot.hOcc 560
  · exact hroot.hOcc 668
  · exact hroot.hOcc 671
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (38 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30

end QiushiMatmul
