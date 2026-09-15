import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0066Refs : Fin 49 → RowRef 726 49 := ![.occ 82, .occ 100, .occ 106, .occ 112, .occ 117, .occ 133, .occ 152, .occ 232, .occ 248, .occ 255, .occ 299, .occ 363, .occ 388, .occ 424, .occ 438, .occ 451, .occ 465, .occ 483, .occ 485, .occ 486, .occ 511, .occ 513, .occ 515, .occ 528, .occ 541, .occ 543, .occ 613, .occ 631, .occ 632, .occ 635, .occ 640, .occ 641, .occ 648, .occ 651, .occ 653, .occ 661, .occ 707, .occ 713, .occ 715, .occ 722, .sumGe, .nonneg 33, .nonneg 40, .branchLe 31 (0), .branchLe 16 (0), .branchGe 27 (1), .branchGe 11 (1), .branchGe 44 (1), .branchGe 6 (1)]

def plane491GenLeaf0066Mult : Fin 49 → Nat := ![485, 3102, 4265, 44, 110, 485, 22, 220, 1522, 301, 44, 22, 1999, 110, 1753, 984, 22, 37, 296, 110, 88, 634, 2942, 3727, 110, 22, 20, 1627, 840, 719, 186, 556, 933, 1784, 203, 110, 75, 73, 203, 22, 4265, 140, 1615, 3124, 776, 8115, 14076, 11736, 17259]

theorem plane491GenLeaf0066 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_44 : (1 : Int) ≤ x 44)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0066Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0066Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0066Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0066Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 82
  · exact hroot.hOcc 100
  · exact hroot.hOcc 106
  · exact hroot.hOcc 112
  · exact hroot.hOcc 117
  · exact hroot.hOcc 133
  · exact hroot.hOcc 152
  · exact hroot.hOcc 232
  · exact hroot.hOcc 248
  · exact hroot.hOcc 255
  · exact hroot.hOcc 299
  · exact hroot.hOcc 363
  · exact hroot.hOcc 388
  · exact hroot.hOcc 424
  · exact hroot.hOcc 438
  · exact hroot.hOcc 451
  · exact hroot.hOcc 465
  · exact hroot.hOcc 483
  · exact hroot.hOcc 485
  · exact hroot.hOcc 486
  · exact hroot.hOcc 511
  · exact hroot.hOcc 513
  · exact hroot.hOcc 515
  · exact hroot.hOcc 528
  · exact hroot.hOcc 541
  · exact hroot.hOcc 543
  · exact hroot.hOcc 613
  · exact hroot.hOcc 631
  · exact hroot.hOcc 632
  · exact hroot.hOcc 635
  · exact hroot.hOcc 640
  · exact hroot.hOcc 641
  · exact hroot.hOcc 648
  · exact hroot.hOcc 651
  · exact hroot.hOcc 653
  · exact hroot.hOcc 661
  · exact hroot.hOcc 707
  · exact hroot.hOcc 713
  · exact hroot.hOcc 715
  · exact hroot.hOcc 722
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (33 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (40 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (11 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11
  · change (∑ k, (if k = (44 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_44
  · change (∑ k, (if k = (6 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6

end QiushiMatmul
