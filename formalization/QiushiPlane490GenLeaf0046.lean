import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0046Refs : Fin 41 → RowRef 713 43 := ![.occ 87, .occ 90, .occ 91, .occ 93, .occ 94, .occ 104, .occ 162, .occ 169, .occ 254, .occ 284, .occ 295, .occ 302, .occ 303, .occ 313, .occ 336, .occ 390, .occ 395, .occ 482, .occ 486, .occ 502, .occ 519, .occ 525, .occ 553, .occ 558, .occ 575, .occ 616, .occ 634, .occ 665, .occ 666, .occ 668, .occ 689, .sumGe, .nonneg 19, .nonneg 37, .branchLe 29 (0), .branchLe 4 (0), .branchGe 23 (1), .branchLe 30 (0), .branchLe 28 (0), .branchGe 35 (1), .branchGe 42 (1)]

def plane490GenLeaf0046Mult : Fin 41 → Nat := ![35, 390, 368, 576, 497, 283, 1715, 55, 41, 211, 781, 125, 228, 480, 1912, 1632, 240, 197, 176, 228, 228, 812, 228, 387, 125, 52, 104, 297, 159, 588, 920, 2140, 205, 124, 1715, 1162, 3527, 228, 1525, 4866, 7161]

theorem plane490GenLeaf0046 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0046Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0046Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0046Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0046Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 90
  · exact hroot.hOcc 91
  · exact hroot.hOcc 93
  · exact hroot.hOcc 94
  · exact hroot.hOcc 104
  · exact hroot.hOcc 162
  · exact hroot.hOcc 169
  · exact hroot.hOcc 254
  · exact hroot.hOcc 284
  · exact hroot.hOcc 295
  · exact hroot.hOcc 302
  · exact hroot.hOcc 303
  · exact hroot.hOcc 313
  · exact hroot.hOcc 336
  · exact hroot.hOcc 390
  · exact hroot.hOcc 395
  · exact hroot.hOcc 482
  · exact hroot.hOcc 486
  · exact hroot.hOcc 502
  · exact hroot.hOcc 519
  · exact hroot.hOcc 525
  · exact hroot.hOcc 553
  · exact hroot.hOcc 558
  · exact hroot.hOcc 575
  · exact hroot.hOcc 616
  · exact hroot.hOcc 634
  · exact hroot.hOcc 665
  · exact hroot.hOcc 666
  · exact hroot.hOcc 668
  · exact hroot.hOcc 689
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42

end QiushiMatmul
