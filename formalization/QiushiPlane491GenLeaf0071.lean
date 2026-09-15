import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0071Refs : Fin 50 → RowRef 726 49 := ![.occ 95, .occ 96, .occ 135, .occ 136, .occ 137, .occ 149, .occ 172, .occ 188, .occ 222, .occ 223, .occ 257, .occ 281, .occ 298, .occ 322, .occ 324, .occ 332, .occ 336, .occ 338, .occ 352, .occ 358, .occ 367, .occ 394, .occ 414, .occ 419, .occ 420, .occ 454, .occ 494, .occ 511, .occ 513, .occ 524, .occ 525, .occ 541, .occ 559, .occ 575, .occ 599, .occ 605, .occ 624, .occ 651, .occ 664, .occ 703, .occ 712, .sumGe, .nonneg 40, .nonneg 45, .nonneg 47, .branchLe 31 (0), .branchGe 16 (1), .branchGe 20 (1), .branchLe 38 (0), .branchGe 39 (1)]

def plane491GenLeaf0071Mult : Fin 50 → Nat := ![3073, 7548, 257, 3419, 16598, 10888, 5492, 213, 198, 3743, 3506, 1417, 941, 120, 2716, 3976, 3322, 594, 10093, 671, 7645, 16004, 993, 3757, 2763, 3312, 931, 931, 396, 3010, 12300, 13043, 4277, 198, 12513, 5776, 708, 1761, 4558, 4022, 4595, 26315, 198, 35291, 396, 26315, 139124, 71953, 8516, 46559]

theorem plane491GenLeaf0071 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_38 : x 38 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0071Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0071Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0071Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0071Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 95
  · exact hroot.hOcc 96
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 149
  · exact hroot.hOcc 172
  · exact hroot.hOcc 188
  · exact hroot.hOcc 222
  · exact hroot.hOcc 223
  · exact hroot.hOcc 257
  · exact hroot.hOcc 281
  · exact hroot.hOcc 298
  · exact hroot.hOcc 322
  · exact hroot.hOcc 324
  · exact hroot.hOcc 332
  · exact hroot.hOcc 336
  · exact hroot.hOcc 338
  · exact hroot.hOcc 352
  · exact hroot.hOcc 358
  · exact hroot.hOcc 367
  · exact hroot.hOcc 394
  · exact hroot.hOcc 414
  · exact hroot.hOcc 419
  · exact hroot.hOcc 420
  · exact hroot.hOcc 454
  · exact hroot.hOcc 494
  · exact hroot.hOcc 511
  · exact hroot.hOcc 513
  · exact hroot.hOcc 524
  · exact hroot.hOcc 525
  · exact hroot.hOcc 541
  · exact hroot.hOcc 559
  · exact hroot.hOcc 575
  · exact hroot.hOcc 599
  · exact hroot.hOcc 605
  · exact hroot.hOcc 624
  · exact hroot.hOcc 651
  · exact hroot.hOcc 664
  · exact hroot.hOcc 703
  · exact hroot.hOcc 712
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (40 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (45 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (47 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (20 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20
  · change (∑ k, (if k = (38 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (39 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39

end QiushiMatmul
