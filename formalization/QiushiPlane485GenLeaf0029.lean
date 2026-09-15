import QiushiPlane485GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane485GenLeaf0029Refs : Fin 39 → RowRef 421 41 := ![.occ 87, .occ 94, .occ 96, .occ 101, .occ 102, .occ 122, .occ 136, .occ 137, .occ 140, .occ 152, .occ 171, .occ 184, .occ 207, .occ 213, .occ 218, .occ 235, .occ 238, .occ 252, .occ 257, .occ 264, .occ 285, .occ 312, .occ 316, .occ 345, .occ 367, .occ 389, .occ 404, .occ 408, .occ 417, .sumGe, .nonneg 0, .branchGe 28 (1), .branchLe 19 (0), .branchLe 22 (0), .branchLe 35 (0), .branchLe 6 (0), .branchLe 32 (0), .branchLe 29 (0), .branchGe 14 (1)]

def plane485GenLeaf0029Mult : Fin 39 → Nat := ![13, 9, 33, 11, 23, 16, 7, 21, 15, 7, 18, 23, 26, 5, 5, 1, 28, 31, 10, 33, 2, 8, 25, 8, 10, 2, 5, 10, 6, 64, 3, 124, 63, 35, 22, 55, 49, 59, 169]

theorem plane485GenLeaf0029 (x : Fin 41 → Int)
    (hroot : plane485GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane485GenLeaf0029Refs i).resolveCoeff plane485GenOccSys j)
    (fun i => (plane485GenLeaf0029Refs i).resolveRhs plane485GenOccSys) plane485GenLeaf0029Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane485GenLeaf0029Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 94
  · exact hroot.hOcc 96
  · exact hroot.hOcc 101
  · exact hroot.hOcc 102
  · exact hroot.hOcc 122
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 140
  · exact hroot.hOcc 152
  · exact hroot.hOcc 171
  · exact hroot.hOcc 184
  · exact hroot.hOcc 207
  · exact hroot.hOcc 213
  · exact hroot.hOcc 218
  · exact hroot.hOcc 235
  · exact hroot.hOcc 238
  · exact hroot.hOcc 252
  · exact hroot.hOcc 257
  · exact hroot.hOcc 264
  · exact hroot.hOcc 285
  · exact hroot.hOcc 312
  · exact hroot.hOcc 316
  · exact hroot.hOcc 345
  · exact hroot.hOcc 367
  · exact hroot.hOcc 389
  · exact hroot.hOcc 404
  · exact hroot.hOcc 408
  · exact hroot.hOcc 417
  · change (∑ j, (-1 : Int) * x j) ≤ -plane485GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (28 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (19 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (22 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (35 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (6 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (32 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (29 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (14 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14

end QiushiMatmul
