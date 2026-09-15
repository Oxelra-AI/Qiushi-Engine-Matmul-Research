import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0102Refs : Fin 44 → RowRef 713 43 := ![.occ 86, .occ 89, .occ 90, .occ 95, .occ 105, .occ 108, .occ 160, .occ 194, .occ 223, .occ 266, .occ 281, .occ 291, .occ 295, .occ 302, .occ 335, .occ 344, .occ 354, .occ 362, .occ 446, .occ 494, .occ 532, .occ 533, .occ 548, .occ 582, .occ 602, .occ 611, .occ 632, .occ 653, .occ 662, .occ 665, .occ 670, .occ 671, .occ 680, .occ 712, .sumGe, .nonneg 15, .nonneg 34, .branchGe 29 (1), .branchGe 18 (1), .branchLe 14 (0), .branchGe 1 (1), .branchLe 20 (0), .branchLe 12 (0), .branchGe 33 (1)]

def plane490GenLeaf0102Mult : Fin 44 → Nat := ![952, 210, 93, 87, 2217, 2325, 13, 436, 477, 488, 723, 2204, 224, 834, 514, 187, 169, 379, 314, 37, 863, 37, 859, 400, 760, 995, 500, 934, 66, 893, 249, 25, 1146, 12, 3188, 1, 12, 5307, 6254, 2288, 649, 3085, 3019, 9897]

theorem plane490GenLeaf0102 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_33 : (1 : Int) ≤ x 33)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0102Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0102Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0102Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0102Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 86
  · exact hroot.hOcc 89
  · exact hroot.hOcc 90
  · exact hroot.hOcc 95
  · exact hroot.hOcc 105
  · exact hroot.hOcc 108
  · exact hroot.hOcc 160
  · exact hroot.hOcc 194
  · exact hroot.hOcc 223
  · exact hroot.hOcc 266
  · exact hroot.hOcc 281
  · exact hroot.hOcc 291
  · exact hroot.hOcc 295
  · exact hroot.hOcc 302
  · exact hroot.hOcc 335
  · exact hroot.hOcc 344
  · exact hroot.hOcc 354
  · exact hroot.hOcc 362
  · exact hroot.hOcc 446
  · exact hroot.hOcc 494
  · exact hroot.hOcc 532
  · exact hroot.hOcc 533
  · exact hroot.hOcc 548
  · exact hroot.hOcc 582
  · exact hroot.hOcc 602
  · exact hroot.hOcc 611
  · exact hroot.hOcc 632
  · exact hroot.hOcc 653
  · exact hroot.hOcc 662
  · exact hroot.hOcc 665
  · exact hroot.hOcc 670
  · exact hroot.hOcc 671
  · exact hroot.hOcc 680
  · exact hroot.hOcc 712
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 34
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (12 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (33 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_33

end QiushiMatmul
