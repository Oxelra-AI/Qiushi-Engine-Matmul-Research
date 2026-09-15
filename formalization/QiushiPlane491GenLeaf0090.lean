import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0090Refs : Fin 50 → RowRef 726 49 := ![.occ 98, .occ 99, .occ 103, .occ 121, .occ 175, .occ 187, .occ 204, .occ 220, .occ 248, .occ 254, .occ 257, .occ 264, .occ 284, .occ 319, .occ 323, .occ 334, .occ 341, .occ 350, .occ 353, .occ 357, .occ 377, .occ 426, .occ 457, .occ 482, .occ 487, .occ 508, .occ 548, .occ 564, .occ 565, .occ 566, .occ 570, .occ 607, .occ 630, .occ 653, .occ 654, .occ 662, .occ 680, .occ 711, .occ 718, .occ 722, .sumGe, .nonneg 22, .nonneg 33, .branchGe 31 (1), .branchLe 44 (0), .branchGe 11 (1), .branchLe 2 (0), .branchLe 7 (0), .branchLe 39 (0), .branchGe 38 (1)]

def plane491GenLeaf0090Mult : Fin 50 → Nat := ![1106, 956, 528, 757, 60, 47, 182, 72, 423, 24, 120, 231, 110, 143, 773, 135, 259, 27, 95, 130, 242, 444, 163, 39, 192, 163, 42, 419, 39, 41, 1, 72, 345, 44, 117, 146, 449, 91, 8, 315, 1159, 655, 30, 3361, 399, 4192, 723, 255, 1158, 2831]

theorem plane491GenLeaf0090 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0090Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0090Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0090Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0090Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 98
  · exact hroot.hOcc 99
  · exact hroot.hOcc 103
  · exact hroot.hOcc 121
  · exact hroot.hOcc 175
  · exact hroot.hOcc 187
  · exact hroot.hOcc 204
  · exact hroot.hOcc 220
  · exact hroot.hOcc 248
  · exact hroot.hOcc 254
  · exact hroot.hOcc 257
  · exact hroot.hOcc 264
  · exact hroot.hOcc 284
  · exact hroot.hOcc 319
  · exact hroot.hOcc 323
  · exact hroot.hOcc 334
  · exact hroot.hOcc 341
  · exact hroot.hOcc 350
  · exact hroot.hOcc 353
  · exact hroot.hOcc 357
  · exact hroot.hOcc 377
  · exact hroot.hOcc 426
  · exact hroot.hOcc 457
  · exact hroot.hOcc 482
  · exact hroot.hOcc 487
  · exact hroot.hOcc 508
  · exact hroot.hOcc 548
  · exact hroot.hOcc 564
  · exact hroot.hOcc 565
  · exact hroot.hOcc 566
  · exact hroot.hOcc 570
  · exact hroot.hOcc 607
  · exact hroot.hOcc 630
  · exact hroot.hOcc 653
  · exact hroot.hOcc 654
  · exact hroot.hOcc 662
  · exact hroot.hOcc 680
  · exact hroot.hOcc 711
  · exact hroot.hOcc 718
  · exact hroot.hOcc 722
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (22 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (33 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (11 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11
  · change (∑ k, (if k = (2 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (7 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (39 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (38 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38

end QiushiMatmul
