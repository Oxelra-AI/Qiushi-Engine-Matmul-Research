import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0030Refs : Fin 42 → RowRef 713 43 := ![.occ 94, .occ 106, .occ 110, .occ 113, .occ 141, .occ 146, .occ 207, .occ 234, .occ 267, .occ 302, .occ 332, .occ 379, .occ 447, .occ 459, .occ 491, .occ 494, .occ 499, .occ 500, .occ 518, .occ 588, .occ 600, .occ 648, .occ 653, .occ 654, .occ 694, .occ 704, .occ 710, .sumGe, .nonneg 25, .branchLe 29 (0), .branchLe 4 (0), .branchGe 23 (1), .branchLe 30 (0), .branchLe 28 (0), .branchLe 35 (0), .branchLe 5 (0), .branchLe 38 (0), .branchGe 15 (1), .branchLe 3 (0), .branchLe 14 (0), .branchLe 24 (0), .branchLe 42 (0)]

def plane490GenLeaf0030Mult : Fin 42 → Nat := ![150, 53, 44, 96, 36, 36, 78, 26, 16, 104, 22, 99, 50, 27, 43, 7, 38, 40, 23, 17, 1, 52, 6, 14, 27, 88, 56, 254, 8, 221, 254, 202, 154, 238, 227, 89, 143, 256, 110, 254, 224, 254]

theorem plane490GenLeaf0030 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0030Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0030Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0030Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0030Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 94
  · exact hroot.hOcc 106
  · exact hroot.hOcc 110
  · exact hroot.hOcc 113
  · exact hroot.hOcc 141
  · exact hroot.hOcc 146
  · exact hroot.hOcc 207
  · exact hroot.hOcc 234
  · exact hroot.hOcc 267
  · exact hroot.hOcc 302
  · exact hroot.hOcc 332
  · exact hroot.hOcc 379
  · exact hroot.hOcc 447
  · exact hroot.hOcc 459
  · exact hroot.hOcc 491
  · exact hroot.hOcc 494
  · exact hroot.hOcc 499
  · exact hroot.hOcc 500
  · exact hroot.hOcc 518
  · exact hroot.hOcc 588
  · exact hroot.hOcc 600
  · exact hroot.hOcc 648
  · exact hroot.hOcc 653
  · exact hroot.hOcc 654
  · exact hroot.hOcc 694
  · exact hroot.hOcc 704
  · exact hroot.hOcc 710
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (38 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42

end QiushiMatmul
