import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0085Refs : Fin 44 → RowRef 713 43 := ![.occ 86, .occ 89, .occ 90, .occ 91, .occ 93, .occ 102, .occ 105, .occ 108, .occ 115, .occ 127, .occ 160, .occ 161, .occ 194, .occ 195, .occ 225, .occ 248, .occ 258, .occ 280, .occ 290, .occ 294, .occ 350, .occ 375, .occ 417, .occ 454, .occ 471, .occ 472, .occ 497, .occ 511, .occ 517, .occ 653, .occ 670, .occ 679, .occ 698, .occ 701, .sumGe, .branchGe 29 (1), .branchLe 18 (0), .branchLe 12 (0), .branchLe 22 (0), .branchGe 1 (1), .branchLe 42 (0), .branchLe 32 (0), .branchGe 8 (1), .branchGe 23 (1)]

def plane490GenLeaf0085Mult : Fin 44 → Nat := ![1, 2, 10, 5, 2, 1, 7, 15, 8, 5, 8, 6, 1, 1, 4, 8, 15, 4, 2, 3, 3, 2, 1, 7, 3, 10, 5, 7, 1, 5, 1, 7, 5, 10, 25, 60, 20, 17, 25, 36, 21, 18, 55, 35]

theorem plane490GenLeaf0085 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0085Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0085Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0085Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0085Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 86
  · exact hroot.hOcc 89
  · exact hroot.hOcc 90
  · exact hroot.hOcc 91
  · exact hroot.hOcc 93
  · exact hroot.hOcc 102
  · exact hroot.hOcc 105
  · exact hroot.hOcc 108
  · exact hroot.hOcc 115
  · exact hroot.hOcc 127
  · exact hroot.hOcc 160
  · exact hroot.hOcc 161
  · exact hroot.hOcc 194
  · exact hroot.hOcc 195
  · exact hroot.hOcc 225
  · exact hroot.hOcc 248
  · exact hroot.hOcc 258
  · exact hroot.hOcc 280
  · exact hroot.hOcc 290
  · exact hroot.hOcc 294
  · exact hroot.hOcc 350
  · exact hroot.hOcc 375
  · exact hroot.hOcc 417
  · exact hroot.hOcc 454
  · exact hroot.hOcc 471
  · exact hroot.hOcc 472
  · exact hroot.hOcc 497
  · exact hroot.hOcc 511
  · exact hroot.hOcc 517
  · exact hroot.hOcc 653
  · exact hroot.hOcc 670
  · exact hroot.hOcc 679
  · exact hroot.hOcc 698
  · exact hroot.hOcc 701
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (12 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23

end QiushiMatmul
