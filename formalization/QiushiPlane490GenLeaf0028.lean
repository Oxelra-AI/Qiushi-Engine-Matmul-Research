import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0028Refs : Fin 44 → RowRef 713 43 := ![.occ 84, .occ 89, .occ 90, .occ 93, .occ 100, .occ 106, .occ 114, .occ 117, .occ 123, .occ 146, .occ 163, .occ 267, .occ 284, .occ 302, .occ 314, .occ 325, .occ 328, .occ 336, .occ 450, .occ 494, .occ 495, .occ 499, .occ 500, .occ 501, .occ 506, .occ 518, .occ 526, .occ 533, .occ 645, .occ 680, .occ 710, .sumGe, .branchLe 29 (0), .branchLe 4 (0), .branchGe 23 (1), .branchLe 30 (0), .branchLe 28 (0), .branchLe 35 (0), .branchLe 5 (0), .branchLe 38 (0), .branchLe 25 (0), .branchLe 15 (0), .branchLe 24 (0), .branchGe 26 (1)]

def plane490GenLeaf0028Mult : Fin 44 → Nat := ![475, 2684, 1322, 3114, 4201, 139, 750, 1736, 401, 1, 375, 1156, 649, 219, 177, 243, 965, 7, 413, 430, 2239, 2038, 7, 445, 1069, 1708, 2673, 1406, 1385, 434, 4, 5791, 5346, 5791, 1062, 2930, 4201, 5791, 5142, 4708, 4725, 5791, 3653, 11351]

theorem plane490GenLeaf0028 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0028Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0028Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0028Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0028Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 84
  · exact hroot.hOcc 89
  · exact hroot.hOcc 90
  · exact hroot.hOcc 93
  · exact hroot.hOcc 100
  · exact hroot.hOcc 106
  · exact hroot.hOcc 114
  · exact hroot.hOcc 117
  · exact hroot.hOcc 123
  · exact hroot.hOcc 146
  · exact hroot.hOcc 163
  · exact hroot.hOcc 267
  · exact hroot.hOcc 284
  · exact hroot.hOcc 302
  · exact hroot.hOcc 314
  · exact hroot.hOcc 325
  · exact hroot.hOcc 328
  · exact hroot.hOcc 336
  · exact hroot.hOcc 450
  · exact hroot.hOcc 494
  · exact hroot.hOcc 495
  · exact hroot.hOcc 499
  · exact hroot.hOcc 500
  · exact hroot.hOcc 501
  · exact hroot.hOcc 506
  · exact hroot.hOcc 518
  · exact hroot.hOcc 526
  · exact hroot.hOcc 533
  · exact hroot.hOcc 645
  · exact hroot.hOcc 680
  · exact hroot.hOcc 710
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (38 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26

end QiushiMatmul
