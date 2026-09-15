import QiushiPlane485GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane485GenLeaf0022Refs : Fin 42 → RowRef 421 41 := ![.occ 93, .occ 100, .occ 118, .occ 126, .occ 130, .occ 135, .occ 139, .occ 140, .occ 146, .occ 150, .occ 151, .occ 162, .occ 164, .occ 166, .occ 175, .occ 177, .occ 182, .occ 195, .occ 207, .occ 210, .occ 224, .occ 252, .occ 265, .occ 297, .occ 312, .occ 313, .occ 335, .occ 339, .occ 362, .occ 372, .occ 393, .occ 404, .occ 413, .sumGe, .nonneg 0, .nonneg 12, .branchLe 28 (0), .branchGe 21 (1), .branchLe 32 (0), .branchLe 25 (0), .branchLe 23 (0), .branchGe 1 (1)]

def plane485GenLeaf0022Mult : Fin 42 → Nat := ![20, 126, 9, 6, 3, 68, 129, 152, 327, 361, 12, 116, 42, 152, 69, 56, 4, 33, 77, 96, 27, 67, 32, 53, 126, 26, 140, 73, 54, 55, 37, 69, 71, 469, 39, 106, 400, 1311, 373, 77, 297, 946]

theorem plane485GenLeaf0022 (x : Fin 41 → Int)
    (hroot : plane485GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane485GenLeaf0022Refs i).resolveCoeff plane485GenOccSys j)
    (fun i => (plane485GenLeaf0022Refs i).resolveRhs plane485GenOccSys) plane485GenLeaf0022Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane485GenLeaf0022Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 93
  · exact hroot.hOcc 100
  · exact hroot.hOcc 118
  · exact hroot.hOcc 126
  · exact hroot.hOcc 130
  · exact hroot.hOcc 135
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 146
  · exact hroot.hOcc 150
  · exact hroot.hOcc 151
  · exact hroot.hOcc 162
  · exact hroot.hOcc 164
  · exact hroot.hOcc 166
  · exact hroot.hOcc 175
  · exact hroot.hOcc 177
  · exact hroot.hOcc 182
  · exact hroot.hOcc 195
  · exact hroot.hOcc 207
  · exact hroot.hOcc 210
  · exact hroot.hOcc 224
  · exact hroot.hOcc 252
  · exact hroot.hOcc 265
  · exact hroot.hOcc 297
  · exact hroot.hOcc 312
  · exact hroot.hOcc 313
  · exact hroot.hOcc 335
  · exact hroot.hOcc 339
  · exact hroot.hOcc 362
  · exact hroot.hOcc 372
  · exact hroot.hOcc 393
  · exact hroot.hOcc 404
  · exact hroot.hOcc 413
  · change (∑ j, (-1 : Int) * x j) ≤ -plane485GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (12 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (28 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (21 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21
  · change (∑ k, (if k = (32 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (25 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (23 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (1 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1

end QiushiMatmul
