import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0038Refs : Fin 44 → RowRef 713 43 := ![.occ 87, .occ 100, .occ 106, .occ 107, .occ 113, .occ 182, .occ 185, .occ 192, .occ 197, .occ 198, .occ 239, .occ 279, .occ 284, .occ 295, .occ 302, .occ 303, .occ 375, .occ 399, .occ 429, .occ 439, .occ 447, .occ 462, .occ 468, .occ 469, .occ 519, .occ 533, .occ 575, .occ 617, .occ 660, .occ 670, .occ 694, .occ 704, .sumGe, .nonneg 40, .branchLe 29 (0), .branchLe 4 (0), .branchGe 23 (1), .branchLe 30 (0), .branchLe 28 (0), .branchLe 35 (0), .branchGe 5 (1), .branchLe 19 (0), .branchGe 39 (1), .branchLe 16 (0)]

def plane490GenLeaf0038Mult : Fin 44 → Nat := ![336, 457, 68, 102, 158, 109, 185, 67, 354, 155, 144, 335, 515, 36, 221, 251, 190, 69, 78, 106, 124, 148, 101, 31, 66, 185, 148, 83, 41, 295, 157, 70, 884, 114, 806, 848, 719, 727, 35, 634, 1815, 666, 478, 884]

theorem plane490GenLeaf0038 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0038Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0038Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0038Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0038Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 100
  · exact hroot.hOcc 106
  · exact hroot.hOcc 107
  · exact hroot.hOcc 113
  · exact hroot.hOcc 182
  · exact hroot.hOcc 185
  · exact hroot.hOcc 192
  · exact hroot.hOcc 197
  · exact hroot.hOcc 198
  · exact hroot.hOcc 239
  · exact hroot.hOcc 279
  · exact hroot.hOcc 284
  · exact hroot.hOcc 295
  · exact hroot.hOcc 302
  · exact hroot.hOcc 303
  · exact hroot.hOcc 375
  · exact hroot.hOcc 399
  · exact hroot.hOcc 429
  · exact hroot.hOcc 439
  · exact hroot.hOcc 447
  · exact hroot.hOcc 462
  · exact hroot.hOcc 468
  · exact hroot.hOcc 469
  · exact hroot.hOcc 519
  · exact hroot.hOcc 533
  · exact hroot.hOcc 575
  · exact hroot.hOcc 617
  · exact hroot.hOcc 660
  · exact hroot.hOcc 670
  · exact hroot.hOcc 694
  · exact hroot.hOcc 704
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (40 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (39 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16

end QiushiMatmul
