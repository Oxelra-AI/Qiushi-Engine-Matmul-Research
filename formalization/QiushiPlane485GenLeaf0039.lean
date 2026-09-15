import QiushiPlane485GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane485GenLeaf0039Refs : Fin 41 → RowRef 421 41 := ![.occ 89, .occ 135, .occ 136, .occ 143, .occ 147, .occ 150, .occ 153, .occ 155, .occ 166, .occ 169, .occ 171, .occ 174, .occ 178, .occ 182, .occ 184, .occ 190, .occ 194, .occ 210, .occ 212, .occ 218, .occ 238, .occ 243, .occ 245, .occ 264, .occ 288, .occ 299, .occ 320, .occ 333, .occ 338, .occ 346, .occ 379, .occ 402, .occ 415, .sumGe, .nonneg 0, .nonneg 3, .nonneg 7, .nonneg 23, .branchGe 28 (1), .branchGe 19 (1), .branchGe 18 (1)]

def plane485GenLeaf0039Mult : Fin 41 → Nat := ![169, 919, 513, 174, 783, 833, 143, 349, 118, 206, 1030, 473, 1750, 434, 110, 321, 922, 491, 206, 2658, 206, 1917, 618, 495, 377, 897, 281, 308, 1740, 423, 177, 329, 514, 3172, 1375, 164, 772, 915, 11651, 4486, 8344]

theorem plane485GenLeaf0039 (x : Fin 41 → Int)
    (hroot : plane485GenOccSys.RootHolds x)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_28 : (1 : Int) ≤ x 28)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane485GenLeaf0039Refs i).resolveCoeff plane485GenOccSys j)
    (fun i => (plane485GenLeaf0039Refs i).resolveRhs plane485GenOccSys) plane485GenLeaf0039Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane485GenLeaf0039Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 89
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 143
  · exact hroot.hOcc 147
  · exact hroot.hOcc 150
  · exact hroot.hOcc 153
  · exact hroot.hOcc 155
  · exact hroot.hOcc 166
  · exact hroot.hOcc 169
  · exact hroot.hOcc 171
  · exact hroot.hOcc 174
  · exact hroot.hOcc 178
  · exact hroot.hOcc 182
  · exact hroot.hOcc 184
  · exact hroot.hOcc 190
  · exact hroot.hOcc 194
  · exact hroot.hOcc 210
  · exact hroot.hOcc 212
  · exact hroot.hOcc 218
  · exact hroot.hOcc 238
  · exact hroot.hOcc 243
  · exact hroot.hOcc 245
  · exact hroot.hOcc 264
  · exact hroot.hOcc 288
  · exact hroot.hOcc 299
  · exact hroot.hOcc 320
  · exact hroot.hOcc 333
  · exact hroot.hOcc 338
  · exact hroot.hOcc 346
  · exact hroot.hOcc 379
  · exact hroot.hOcc 402
  · exact hroot.hOcc 415
  · change (∑ j, (-1 : Int) * x j) ≤ -plane485GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (3 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (7 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (23 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (28 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (19 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (18 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18

end QiushiMatmul
