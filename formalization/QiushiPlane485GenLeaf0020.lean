import QiushiPlane485GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane485GenLeaf0020Refs : Fin 41 → RowRef 421 41 := ![.occ 87, .occ 94, .occ 96, .occ 106, .occ 107, .occ 109, .occ 120, .occ 135, .occ 136, .occ 153, .occ 156, .occ 162, .occ 164, .occ 175, .occ 184, .occ 190, .occ 224, .occ 232, .occ 234, .occ 235, .occ 238, .occ 246, .occ 252, .occ 265, .occ 272, .occ 276, .occ 280, .occ 293, .occ 313, .occ 332, .occ 346, .occ 375, .occ 393, .occ 401, .sumGe, .nonneg 0, .nonneg 12, .branchLe 28 (0), .branchLe 21 (0), .branchGe 14 (1), .branchGe 29 (1)]

def plane485GenLeaf0020Mult : Fin 41 → Nat := ![122, 139, 139, 238, 308, 105, 355, 163, 155, 167, 50, 21, 39, 61, 117, 333, 60, 42, 135, 92, 100, 61, 113, 75, 269, 153, 17, 30, 117, 17, 26, 193, 141, 5, 511, 85, 8, 411, 430, 1784, 1517]

theorem plane485GenLeaf0020 (x : Fin 41 → Int)
    (hroot : plane485GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane485GenLeaf0020Refs i).resolveCoeff plane485GenOccSys j)
    (fun i => (plane485GenLeaf0020Refs i).resolveRhs plane485GenOccSys) plane485GenLeaf0020Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane485GenLeaf0020Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 94
  · exact hroot.hOcc 96
  · exact hroot.hOcc 106
  · exact hroot.hOcc 107
  · exact hroot.hOcc 109
  · exact hroot.hOcc 120
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 153
  · exact hroot.hOcc 156
  · exact hroot.hOcc 162
  · exact hroot.hOcc 164
  · exact hroot.hOcc 175
  · exact hroot.hOcc 184
  · exact hroot.hOcc 190
  · exact hroot.hOcc 224
  · exact hroot.hOcc 232
  · exact hroot.hOcc 234
  · exact hroot.hOcc 235
  · exact hroot.hOcc 238
  · exact hroot.hOcc 246
  · exact hroot.hOcc 252
  · exact hroot.hOcc 265
  · exact hroot.hOcc 272
  · exact hroot.hOcc 276
  · exact hroot.hOcc 280
  · exact hroot.hOcc 293
  · exact hroot.hOcc 313
  · exact hroot.hOcc 332
  · exact hroot.hOcc 346
  · exact hroot.hOcc 375
  · exact hroot.hOcc 393
  · exact hroot.hOcc 401
  · change (∑ j, (-1 : Int) * x j) ≤ -plane485GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (12 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (28 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (21 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (14 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (29 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29

end QiushiMatmul
