import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0012Refs : Fin 44 → RowRef 713 43 := ![.occ 84, .occ 112, .occ 113, .occ 139, .occ 143, .occ 150, .occ 155, .occ 171, .occ 211, .occ 234, .occ 250, .occ 252, .occ 253, .occ 283, .occ 284, .occ 293, .occ 295, .occ 303, .occ 314, .occ 322, .occ 325, .occ 364, .occ 389, .occ 529, .occ 530, .occ 539, .occ 554, .occ 619, .occ 632, .occ 649, .occ 673, .occ 678, .occ 690, .occ 693, .sumGe, .nonneg 37, .branchLe 29 (0), .branchLe 4 (0), .branchLe 23 (0), .branchLe 16 (0), .branchGe 39 (1), .branchLe 17 (0), .branchGe 22 (1), .branchGe 30 (1)]

def plane490GenLeaf0012Mult : Fin 44 → Nat := ![6724, 543, 15617, 2612, 1295, 3163, 11944, 3466, 3044, 8613, 5930, 17694, 2697, 887, 5938, 523, 2069, 316, 1404, 1947, 430, 11970, 19102, 5408, 1290, 3689, 1287, 1860, 3235, 5930, 1720, 3549, 9707, 887, 24511, 21992, 4752, 20722, 24511, 22564, 8109, 2082, 68571, 73610]

theorem plane490GenLeaf0012 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0012Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0012Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0012Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0012Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 84
  · exact hroot.hOcc 112
  · exact hroot.hOcc 113
  · exact hroot.hOcc 139
  · exact hroot.hOcc 143
  · exact hroot.hOcc 150
  · exact hroot.hOcc 155
  · exact hroot.hOcc 171
  · exact hroot.hOcc 211
  · exact hroot.hOcc 234
  · exact hroot.hOcc 250
  · exact hroot.hOcc 252
  · exact hroot.hOcc 253
  · exact hroot.hOcc 283
  · exact hroot.hOcc 284
  · exact hroot.hOcc 293
  · exact hroot.hOcc 295
  · exact hroot.hOcc 303
  · exact hroot.hOcc 314
  · exact hroot.hOcc 322
  · exact hroot.hOcc 325
  · exact hroot.hOcc 364
  · exact hroot.hOcc 389
  · exact hroot.hOcc 529
  · exact hroot.hOcc 530
  · exact hroot.hOcc 539
  · exact hroot.hOcc 554
  · exact hroot.hOcc 619
  · exact hroot.hOcc 632
  · exact hroot.hOcc 649
  · exact hroot.hOcc 673
  · exact hroot.hOcc 678
  · exact hroot.hOcc 690
  · exact hroot.hOcc 693
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (39 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30

end QiushiMatmul
