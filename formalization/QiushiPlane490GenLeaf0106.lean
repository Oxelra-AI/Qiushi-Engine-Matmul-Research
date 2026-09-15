import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0106Refs : Fin 42 → RowRef 713 43 := ![.occ 89, .occ 90, .occ 91, .occ 94, .occ 105, .occ 106, .occ 108, .occ 116, .occ 141, .occ 146, .occ 159, .occ 237, .occ 250, .occ 299, .occ 304, .occ 326, .occ 332, .occ 349, .occ 354, .occ 446, .occ 479, .occ 494, .occ 538, .occ 542, .occ 550, .occ 562, .occ 582, .occ 594, .occ 595, .occ 602, .occ 608, .occ 609, .occ 655, .occ 706, .sumGe, .branchGe 29 (1), .branchGe 18 (1), .branchLe 14 (0), .branchGe 1 (1), .branchGe 20 (1), .branchLe 8 (0), .branchLe 2 (0)]

def plane490GenLeaf0106Mult : Fin 42 → Nat := ![7, 51, 8, 38, 107, 96, 79, 19, 48, 48, 87, 52, 33, 37, 23, 5, 53, 8, 24, 10, 24, 47, 29, 3, 34, 104, 39, 2, 14, 61, 55, 68, 6, 2, 167, 536, 430, 127, 29, 466, 120, 104]

theorem plane490GenLeaf0106 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0106Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0106Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0106Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0106Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 89
  · exact hroot.hOcc 90
  · exact hroot.hOcc 91
  · exact hroot.hOcc 94
  · exact hroot.hOcc 105
  · exact hroot.hOcc 106
  · exact hroot.hOcc 108
  · exact hroot.hOcc 116
  · exact hroot.hOcc 141
  · exact hroot.hOcc 146
  · exact hroot.hOcc 159
  · exact hroot.hOcc 237
  · exact hroot.hOcc 250
  · exact hroot.hOcc 299
  · exact hroot.hOcc 304
  · exact hroot.hOcc 326
  · exact hroot.hOcc 332
  · exact hroot.hOcc 349
  · exact hroot.hOcc 354
  · exact hroot.hOcc 446
  · exact hroot.hOcc 479
  · exact hroot.hOcc 494
  · exact hroot.hOcc 538
  · exact hroot.hOcc 542
  · exact hroot.hOcc 550
  · exact hroot.hOcc 562
  · exact hroot.hOcc 582
  · exact hroot.hOcc 594
  · exact hroot.hOcc 595
  · exact hroot.hOcc 602
  · exact hroot.hOcc 608
  · exact hroot.hOcc 609
  · exact hroot.hOcc 655
  · exact hroot.hOcc 706
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2

end QiushiMatmul
