import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0069Refs : Fin 43 → RowRef 713 43 := ![.occ 84, .occ 89, .occ 99, .occ 107, .occ 115, .occ 119, .occ 120, .occ 197, .occ 201, .occ 216, .occ 244, .occ 258, .occ 264, .occ 274, .occ 279, .occ 292, .occ 294, .occ 295, .occ 336, .occ 350, .occ 375, .occ 447, .occ 465, .occ 466, .occ 467, .occ 471, .occ 545, .occ 601, .occ 617, .occ 673, .occ 685, .occ 695, .occ 697, .occ 708, .sumGe, .nonneg 10, .branchLe 29 (0), .branchGe 4 (1), .branchLe 34 (0), .branchGe 23 (1), .branchGe 25 (1), .branchLe 33 (0), .branchGe 5 (1)]

def plane490GenLeaf0069Mult : Fin 43 → Nat := ![20, 45, 76, 17, 18, 25, 23, 4, 13, 16, 48, 30, 12, 21, 58, 11, 32, 26, 13, 13, 32, 2, 11, 3, 2, 12, 16, 16, 16, 5, 10, 1, 1, 24, 77, 13, 32, 185, 30, 88, 232, 32, 241]

theorem plane490GenLeaf0069 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0069Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0069Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0069Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0069Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 84
  · exact hroot.hOcc 89
  · exact hroot.hOcc 99
  · exact hroot.hOcc 107
  · exact hroot.hOcc 115
  · exact hroot.hOcc 119
  · exact hroot.hOcc 120
  · exact hroot.hOcc 197
  · exact hroot.hOcc 201
  · exact hroot.hOcc 216
  · exact hroot.hOcc 244
  · exact hroot.hOcc 258
  · exact hroot.hOcc 264
  · exact hroot.hOcc 274
  · exact hroot.hOcc 279
  · exact hroot.hOcc 292
  · exact hroot.hOcc 294
  · exact hroot.hOcc 295
  · exact hroot.hOcc 336
  · exact hroot.hOcc 350
  · exact hroot.hOcc 375
  · exact hroot.hOcc 447
  · exact hroot.hOcc 465
  · exact hroot.hOcc 466
  · exact hroot.hOcc 467
  · exact hroot.hOcc 471
  · exact hroot.hOcc 545
  · exact hroot.hOcc 601
  · exact hroot.hOcc 617
  · exact hroot.hOcc 673
  · exact hroot.hOcc 685
  · exact hroot.hOcc 695
  · exact hroot.hOcc 697
  · exact hroot.hOcc 708
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25
  · change (∑ k, (if k = (33 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5

end QiushiMatmul
