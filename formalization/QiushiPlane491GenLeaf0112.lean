import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0112Refs : Fin 50 → RowRef 726 49 := ![.occ 82, .occ 87, .occ 98, .occ 105, .occ 112, .occ 113, .occ 118, .occ 123, .occ 144, .occ 149, .occ 151, .occ 155, .occ 163, .occ 170, .occ 186, .occ 243, .occ 255, .occ 318, .occ 328, .occ 335, .occ 350, .occ 351, .occ 358, .occ 379, .occ 393, .occ 430, .occ 495, .occ 516, .occ 553, .occ 611, .occ 631, .occ 640, .occ 652, .occ 653, .occ 661, .occ 662, .occ 692, .occ 722, .occ 723, .sumGe, .nonneg 3, .nonneg 11, .nonneg 15, .nonneg 32, .branchGe 31 (1), .branchGe 44 (1), .branchGe 6 (1), .branchLe 9 (0), .branchGe 14 (1), .branchGe 22 (1)]

def plane491GenLeaf0112Mult : Fin 50 → Nat := ![241, 1834, 769, 349, 1674, 595, 533, 1674, 505, 284, 453, 336, 1287, 12, 16, 129, 426, 236, 186, 355, 370, 185, 291, 364, 730, 129, 150, 57, 459, 213, 252, 1164, 805, 284, 130, 632, 71, 75, 816, 2055, 483, 102, 277, 441, 4673, 4261, 1217, 1980, 3123, 7146]

theorem plane491GenLeaf0112 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_44 : (1 : Int) ≤ x 44)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0112Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0112Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0112Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0112Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 82
  · exact hroot.hOcc 87
  · exact hroot.hOcc 98
  · exact hroot.hOcc 105
  · exact hroot.hOcc 112
  · exact hroot.hOcc 113
  · exact hroot.hOcc 118
  · exact hroot.hOcc 123
  · exact hroot.hOcc 144
  · exact hroot.hOcc 149
  · exact hroot.hOcc 151
  · exact hroot.hOcc 155
  · exact hroot.hOcc 163
  · exact hroot.hOcc 170
  · exact hroot.hOcc 186
  · exact hroot.hOcc 243
  · exact hroot.hOcc 255
  · exact hroot.hOcc 318
  · exact hroot.hOcc 328
  · exact hroot.hOcc 335
  · exact hroot.hOcc 350
  · exact hroot.hOcc 351
  · exact hroot.hOcc 358
  · exact hroot.hOcc 379
  · exact hroot.hOcc 393
  · exact hroot.hOcc 430
  · exact hroot.hOcc 495
  · exact hroot.hOcc 516
  · exact hroot.hOcc 553
  · exact hroot.hOcc 611
  · exact hroot.hOcc 631
  · exact hroot.hOcc 640
  · exact hroot.hOcc 652
  · exact hroot.hOcc 653
  · exact hroot.hOcc 661
  · exact hroot.hOcc 662
  · exact hroot.hOcc 692
  · exact hroot.hOcc 722
  · exact hroot.hOcc 723
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (11 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (15 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (32 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_44
  · change (∑ k, (if k = (6 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (9 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (14 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (22 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22

end QiushiMatmul
