import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0016Refs : Fin 33 → RowRef 371 32 := ![.occ 96, .occ 97, .occ 100, .occ 105, .occ 112, .occ 120, .occ 130, .occ 139, .occ 155, .occ 188, .occ 205, .occ 208, .occ 213, .occ 224, .occ 228, .occ 282, .occ 289, .occ 299, .occ 322, .occ 325, .occ 341, .occ 345, .occ 346, .occ 357, .occ 359, .sumGe, .nonneg 16, .branchLe 14 (0), .branchGe 9 (1), .branchLe 12 (0), .branchLe 17 (0), .branchLe 22 (0), .branchGe 28 (1)]

def plane489GenLeaf0016Mult : Fin 33 → Nat := ![5, 36, 20, 8, 26, 17, 33, 13, 2, 24, 14, 6, 37, 20, 32, 7, 14, 3, 19, 9, 6, 3, 6, 21, 4, 64, 1, 39, 126, 58, 64, 28, 126]

theorem plane489GenLeaf0016 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0016Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0016Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0016Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0016Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 96
  · exact hroot.hOcc 97
  · exact hroot.hOcc 100
  · exact hroot.hOcc 105
  · exact hroot.hOcc 112
  · exact hroot.hOcc 120
  · exact hroot.hOcc 130
  · exact hroot.hOcc 139
  · exact hroot.hOcc 155
  · exact hroot.hOcc 188
  · exact hroot.hOcc 205
  · exact hroot.hOcc 208
  · exact hroot.hOcc 213
  · exact hroot.hOcc 224
  · exact hroot.hOcc 228
  · exact hroot.hOcc 282
  · exact hroot.hOcc 289
  · exact hroot.hOcc 299
  · exact hroot.hOcc 322
  · exact hroot.hOcc 325
  · exact hroot.hOcc 341
  · exact hroot.hOcc 345
  · exact hroot.hOcc 346
  · exact hroot.hOcc 357
  · exact hroot.hOcc 359
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (16 : Fin 32) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (14 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (9 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9
  · change (∑ k, (if k = (12 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (17 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (22 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (28 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28

end QiushiMatmul
