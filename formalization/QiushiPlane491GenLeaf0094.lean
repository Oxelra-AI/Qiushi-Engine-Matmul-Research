import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0094Refs : Fin 50 → RowRef 726 49 := ![.occ 80, .occ 101, .occ 103, .occ 121, .occ 124, .occ 134, .occ 169, .occ 204, .occ 213, .occ 215, .occ 219, .occ 222, .occ 231, .occ 239, .occ 248, .occ 261, .occ 274, .occ 312, .occ 315, .occ 320, .occ 341, .occ 355, .occ 368, .occ 420, .occ 426, .occ 484, .occ 495, .occ 541, .occ 549, .occ 565, .occ 569, .occ 601, .occ 611, .occ 621, .occ 648, .occ 653, .occ 662, .occ 715, .sumGe, .nonneg 16, .nonneg 24, .nonneg 32, .nonneg 33, .branchGe 31 (1), .branchLe 44 (0), .branchGe 11 (1), .branchLe 2 (0), .branchLe 7 (0), .branchGe 39 (1), .branchGe 8 (1)]

def plane491GenLeaf0094Mult : Fin 50 → Nat := ![453, 490, 352, 60, 149, 35, 250, 75, 128, 189, 157, 108, 61, 71, 293, 97, 13, 84, 397, 109, 212, 358, 50, 757, 140, 194, 71, 183, 142, 244, 39, 112, 58, 80, 229, 125, 164, 26, 783, 592, 185, 341, 528, 1289, 712, 2040, 372, 134, 1765, 3037]

theorem plane491GenLeaf0094 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0094Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0094Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0094Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0094Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 80
  · exact hroot.hOcc 101
  · exact hroot.hOcc 103
  · exact hroot.hOcc 121
  · exact hroot.hOcc 124
  · exact hroot.hOcc 134
  · exact hroot.hOcc 169
  · exact hroot.hOcc 204
  · exact hroot.hOcc 213
  · exact hroot.hOcc 215
  · exact hroot.hOcc 219
  · exact hroot.hOcc 222
  · exact hroot.hOcc 231
  · exact hroot.hOcc 239
  · exact hroot.hOcc 248
  · exact hroot.hOcc 261
  · exact hroot.hOcc 274
  · exact hroot.hOcc 312
  · exact hroot.hOcc 315
  · exact hroot.hOcc 320
  · exact hroot.hOcc 341
  · exact hroot.hOcc 355
  · exact hroot.hOcc 368
  · exact hroot.hOcc 420
  · exact hroot.hOcc 426
  · exact hroot.hOcc 484
  · exact hroot.hOcc 495
  · exact hroot.hOcc 541
  · exact hroot.hOcc 549
  · exact hroot.hOcc 565
  · exact hroot.hOcc 569
  · exact hroot.hOcc 601
  · exact hroot.hOcc 611
  · exact hroot.hOcc 621
  · exact hroot.hOcc 648
  · exact hroot.hOcc 653
  · exact hroot.hOcc 662
  · exact hroot.hOcc 715
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (16 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (24 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (32 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (33 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (11 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11
  · change (∑ k, (if k = (2 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (7 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (39 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (8 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8

end QiushiMatmul
