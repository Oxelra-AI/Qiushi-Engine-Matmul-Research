import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0114Refs : Fin 44 → RowRef 713 43 := ![.occ 100, .occ 103, .occ 105, .occ 108, .occ 111, .occ 126, .occ 132, .occ 149, .occ 152, .occ 157, .occ 182, .occ 192, .occ 204, .occ 205, .occ 225, .occ 227, .occ 239, .occ 284, .occ 290, .occ 291, .occ 298, .occ 303, .occ 335, .occ 342, .occ 365, .occ 366, .occ 475, .occ 545, .occ 550, .occ 602, .occ 607, .occ 632, .occ 655, .occ 667, .occ 691, .occ 694, .occ 697, .sumGe, .nonneg 3, .nonneg 4, .branchGe 29 (1), .branchGe 18 (1), .branchGe 14 (1), .branchGe 32 (1)]

def plane490GenLeaf0114Mult : Fin 44 → Nat := ![871, 2488, 1515, 1372, 903, 1271, 386, 443, 237, 187, 1071, 277, 852, 592, 211, 323, 277, 150, 200, 413, 613, 61, 571, 963, 277, 358, 621, 159, 1492, 715, 29, 384, 1034, 243, 462, 179, 715, 2549, 1538, 2001, 7470, 2847, 9522, 8074]

theorem plane490GenLeaf0114 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_32 : (1 : Int) ≤ x 32)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0114Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0114Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0114Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0114Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 100
  · exact hroot.hOcc 103
  · exact hroot.hOcc 105
  · exact hroot.hOcc 108
  · exact hroot.hOcc 111
  · exact hroot.hOcc 126
  · exact hroot.hOcc 132
  · exact hroot.hOcc 149
  · exact hroot.hOcc 152
  · exact hroot.hOcc 157
  · exact hroot.hOcc 182
  · exact hroot.hOcc 192
  · exact hroot.hOcc 204
  · exact hroot.hOcc 205
  · exact hroot.hOcc 225
  · exact hroot.hOcc 227
  · exact hroot.hOcc 239
  · exact hroot.hOcc 284
  · exact hroot.hOcc 290
  · exact hroot.hOcc 291
  · exact hroot.hOcc 298
  · exact hroot.hOcc 303
  · exact hroot.hOcc 335
  · exact hroot.hOcc 342
  · exact hroot.hOcc 365
  · exact hroot.hOcc 366
  · exact hroot.hOcc 475
  · exact hroot.hOcc 545
  · exact hroot.hOcc 550
  · exact hroot.hOcc 602
  · exact hroot.hOcc 607
  · exact hroot.hOcc 632
  · exact hroot.hOcc 655
  · exact hroot.hOcc 667
  · exact hroot.hOcc 691
  · exact hroot.hOcc 694
  · exact hroot.hOcc 697
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (32 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32

end QiushiMatmul
