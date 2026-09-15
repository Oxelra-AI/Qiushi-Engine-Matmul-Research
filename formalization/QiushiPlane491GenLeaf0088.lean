import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0088Refs : Fin 50 → RowRef 726 49 := ![.occ 87, .occ 100, .occ 108, .occ 114, .occ 118, .occ 153, .occ 167, .occ 219, .occ 231, .occ 234, .occ 256, .occ 257, .occ 260, .occ 293, .occ 299, .occ 312, .occ 334, .occ 350, .occ 355, .occ 359, .occ 372, .occ 373, .occ 393, .occ 401, .occ 409, .occ 416, .occ 424, .occ 431, .occ 453, .occ 496, .occ 509, .occ 529, .occ 533, .occ 539, .occ 541, .occ 606, .occ 653, .occ 662, .occ 671, .occ 691, .occ 708, .occ 715, .sumGe, .nonneg 24, .branchGe 31 (1), .branchLe 44 (0), .branchLe 11 (0), .branchGe 27 (1), .branchGe 43 (1), .branchGe 42 (1)]

def plane491GenLeaf0088Mult : Fin 50 → Nat := ![294001, 1281339, 66031, 86447, 17384, 340858, 89705, 326919, 34402, 366870, 92075, 366980, 181829, 402140, 158298, 812675, 304272, 199577, 1488605, 31547, 874295, 13736, 1281085, 242787, 207951, 676615, 245570, 34702, 699824, 27865, 564486, 137493, 198189, 52086, 40774, 31547, 433716, 556971, 653293, 8191, 51900, 34051, 1815524, 2092088, 4097772, 717569, 1183728, 3336879, 2326185, 6182224]

theorem plane491GenLeaf0088 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_43 : (1 : Int) ≤ x 43)
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0088Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0088Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0088Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0088Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 100
  · exact hroot.hOcc 108
  · exact hroot.hOcc 114
  · exact hroot.hOcc 118
  · exact hroot.hOcc 153
  · exact hroot.hOcc 167
  · exact hroot.hOcc 219
  · exact hroot.hOcc 231
  · exact hroot.hOcc 234
  · exact hroot.hOcc 256
  · exact hroot.hOcc 257
  · exact hroot.hOcc 260
  · exact hroot.hOcc 293
  · exact hroot.hOcc 299
  · exact hroot.hOcc 312
  · exact hroot.hOcc 334
  · exact hroot.hOcc 350
  · exact hroot.hOcc 355
  · exact hroot.hOcc 359
  · exact hroot.hOcc 372
  · exact hroot.hOcc 373
  · exact hroot.hOcc 393
  · exact hroot.hOcc 401
  · exact hroot.hOcc 409
  · exact hroot.hOcc 416
  · exact hroot.hOcc 424
  · exact hroot.hOcc 431
  · exact hroot.hOcc 453
  · exact hroot.hOcc 496
  · exact hroot.hOcc 509
  · exact hroot.hOcc 529
  · exact hroot.hOcc 533
  · exact hroot.hOcc 539
  · exact hroot.hOcc 541
  · exact hroot.hOcc 606
  · exact hroot.hOcc 653
  · exact hroot.hOcc 662
  · exact hroot.hOcc 671
  · exact hroot.hOcc 691
  · exact hroot.hOcc 708
  · exact hroot.hOcc 715
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (24 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (11 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (27 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (43 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_43
  · change (∑ k, (if k = (42 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42

end QiushiMatmul
