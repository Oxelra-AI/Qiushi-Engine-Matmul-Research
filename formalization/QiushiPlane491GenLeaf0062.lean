import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0062Refs : Fin 50 → RowRef 726 49 := ![.occ 85, .occ 88, .occ 97, .occ 100, .occ 103, .occ 138, .occ 147, .occ 181, .occ 230, .occ 232, .occ 257, .occ 284, .occ 299, .occ 324, .occ 326, .occ 341, .occ 365, .occ 396, .occ 407, .occ 420, .occ 424, .occ 452, .occ 489, .occ 511, .occ 513, .occ 515, .occ 532, .occ 541, .occ 563, .occ 569, .occ 628, .occ 632, .occ 646, .occ 648, .occ 653, .occ 662, .occ 691, .occ 693, .occ 698, .occ 700, .occ 709, .sumGe, .nonneg 10, .branchLe 31 (0), .branchLe 16 (0), .branchGe 27 (1), .branchGe 11 (1), .branchLe 44 (0), .branchLe 46 (0), .branchGe 18 (1)]

def plane491GenLeaf0062Mult : Fin 50 → Nat := ![14178, 3654, 1253, 510, 7165, 6149, 4764, 1109, 6047, 2389, 829, 8487, 1909, 1602, 492, 2485, 10038, 474, 6097, 1637, 8045, 714, 1559, 568, 1281, 933, 874, 2791, 533, 1704, 1366, 1297, 497, 2290, 8436, 3062, 466, 1016, 1570, 449, 3560, 16957, 7597, 8045, 12529, 34519, 34307, 2484, 13446, 61351]

theorem plane491GenLeaf0062 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_46 : x 46 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0062Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0062Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0062Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0062Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 85
  · exact hroot.hOcc 88
  · exact hroot.hOcc 97
  · exact hroot.hOcc 100
  · exact hroot.hOcc 103
  · exact hroot.hOcc 138
  · exact hroot.hOcc 147
  · exact hroot.hOcc 181
  · exact hroot.hOcc 230
  · exact hroot.hOcc 232
  · exact hroot.hOcc 257
  · exact hroot.hOcc 284
  · exact hroot.hOcc 299
  · exact hroot.hOcc 324
  · exact hroot.hOcc 326
  · exact hroot.hOcc 341
  · exact hroot.hOcc 365
  · exact hroot.hOcc 396
  · exact hroot.hOcc 407
  · exact hroot.hOcc 420
  · exact hroot.hOcc 424
  · exact hroot.hOcc 452
  · exact hroot.hOcc 489
  · exact hroot.hOcc 511
  · exact hroot.hOcc 513
  · exact hroot.hOcc 515
  · exact hroot.hOcc 532
  · exact hroot.hOcc 541
  · exact hroot.hOcc 563
  · exact hroot.hOcc 569
  · exact hroot.hOcc 628
  · exact hroot.hOcc 632
  · exact hroot.hOcc 646
  · exact hroot.hOcc 648
  · exact hroot.hOcc 653
  · exact hroot.hOcc 662
  · exact hroot.hOcc 691
  · exact hroot.hOcc 693
  · exact hroot.hOcc 698
  · exact hroot.hOcc 700
  · exact hroot.hOcc 709
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (11 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11
  · change (∑ k, (if k = (44 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (46 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_46
  · change (∑ k, (if k = (18 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18

end QiushiMatmul
