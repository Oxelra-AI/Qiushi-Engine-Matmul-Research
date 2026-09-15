import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0009Refs : Fin 44 → RowRef 713 43 := ![.occ 84, .occ 85, .occ 86, .occ 89, .occ 91, .occ 107, .occ 185, .occ 198, .occ 206, .occ 236, .occ 249, .occ 283, .occ 286, .occ 293, .occ 295, .occ 314, .occ 354, .occ 355, .occ 364, .occ 378, .occ 390, .occ 395, .occ 532, .occ 599, .occ 607, .occ 613, .occ 641, .occ 666, .occ 668, .occ 673, .occ 683, .occ 687, .sumGe, .nonneg 14, .nonneg 16, .nonneg 37, .branchLe 29 (0), .branchLe 4 (0), .branchLe 23 (0), .branchGe 39 (1), .branchLe 17 (0), .branchLe 22 (0), .branchLe 20 (0), .branchGe 42 (1)]

def plane490GenLeaf0009Mult : Fin 44 → Nat := ![180, 1840, 1296, 723, 192, 249, 48, 368, 36, 161, 6, 1438, 413, 125, 614, 1044, 739, 569, 1251, 554, 1322, 1246, 125, 797, 580, 435, 6, 694, 123, 217, 672, 279, 2855, 362, 36, 368, 1603, 1745, 2732, 1316, 2116, 6, 2855, 8411]

theorem plane490GenLeaf0009 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0009Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0009Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0009Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0009Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 84
  · exact hroot.hOcc 85
  · exact hroot.hOcc 86
  · exact hroot.hOcc 89
  · exact hroot.hOcc 91
  · exact hroot.hOcc 107
  · exact hroot.hOcc 185
  · exact hroot.hOcc 198
  · exact hroot.hOcc 206
  · exact hroot.hOcc 236
  · exact hroot.hOcc 249
  · exact hroot.hOcc 283
  · exact hroot.hOcc 286
  · exact hroot.hOcc 293
  · exact hroot.hOcc 295
  · exact hroot.hOcc 314
  · exact hroot.hOcc 354
  · exact hroot.hOcc 355
  · exact hroot.hOcc 364
  · exact hroot.hOcc 378
  · exact hroot.hOcc 390
  · exact hroot.hOcc 395
  · exact hroot.hOcc 532
  · exact hroot.hOcc 599
  · exact hroot.hOcc 607
  · exact hroot.hOcc 613
  · exact hroot.hOcc 641
  · exact hroot.hOcc 666
  · exact hroot.hOcc 668
  · exact hroot.hOcc 673
  · exact hroot.hOcc 683
  · exact hroot.hOcc 687
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (39 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42

end QiushiMatmul
