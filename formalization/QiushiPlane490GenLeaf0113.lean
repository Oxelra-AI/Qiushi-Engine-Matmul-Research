import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0113Refs : Fin 43 → RowRef 713 43 := ![.occ 93, .occ 100, .occ 105, .occ 108, .occ 126, .occ 133, .occ 159, .occ 168, .occ 170, .occ 173, .occ 203, .occ 250, .occ 283, .occ 290, .occ 298, .occ 321, .occ 335, .occ 336, .occ 354, .occ 365, .occ 376, .occ 437, .occ 442, .occ 446, .occ 480, .occ 505, .occ 517, .occ 520, .occ 521, .occ 597, .occ 602, .occ 605, .occ 606, .occ 646, .occ 688, .occ 692, .sumGe, .nonneg 21, .branchGe 29 (1), .branchGe 18 (1), .branchGe 14 (1), .branchLe 32 (0), .branchGe 38 (1)]

def plane490GenLeaf0113Mult : Fin 43 → Nat := ![5, 93, 118, 120, 32, 118, 78, 35, 113, 10, 58, 43, 30, 5, 103, 34, 79, 55, 20, 15, 42, 29, 3, 35, 49, 10, 14, 39, 34, 13, 45, 41, 5, 64, 6, 1, 163, 101, 703, 207, 583, 64, 448]

theorem plane490GenLeaf0113 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0113Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0113Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0113Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0113Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 93
  · exact hroot.hOcc 100
  · exact hroot.hOcc 105
  · exact hroot.hOcc 108
  · exact hroot.hOcc 126
  · exact hroot.hOcc 133
  · exact hroot.hOcc 159
  · exact hroot.hOcc 168
  · exact hroot.hOcc 170
  · exact hroot.hOcc 173
  · exact hroot.hOcc 203
  · exact hroot.hOcc 250
  · exact hroot.hOcc 283
  · exact hroot.hOcc 290
  · exact hroot.hOcc 298
  · exact hroot.hOcc 321
  · exact hroot.hOcc 335
  · exact hroot.hOcc 336
  · exact hroot.hOcc 354
  · exact hroot.hOcc 365
  · exact hroot.hOcc 376
  · exact hroot.hOcc 437
  · exact hroot.hOcc 442
  · exact hroot.hOcc 446
  · exact hroot.hOcc 480
  · exact hroot.hOcc 505
  · exact hroot.hOcc 517
  · exact hroot.hOcc 520
  · exact hroot.hOcc 521
  · exact hroot.hOcc 597
  · exact hroot.hOcc 602
  · exact hroot.hOcc 605
  · exact hroot.hOcc 606
  · exact hroot.hOcc 646
  · exact hroot.hOcc 688
  · exact hroot.hOcc 692
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (38 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38

end QiushiMatmul
