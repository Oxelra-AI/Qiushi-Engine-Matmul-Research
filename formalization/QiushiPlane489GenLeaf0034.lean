import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0034Refs : Fin 32 → RowRef 371 32 := ![.occ 96, .occ 102, .occ 105, .occ 121, .occ 128, .occ 130, .occ 138, .occ 139, .occ 165, .occ 182, .occ 184, .occ 191, .occ 202, .occ 209, .occ 263, .occ 283, .occ 299, .occ 307, .occ 336, .occ 342, .occ 346, .occ 362, .occ 365, .occ 369, .sumGe, .branchGe 14 (1), .branchLe 26 (0), .branchGe 7 (1), .branchLe 18 (0), .branchGe 31 (1), .branchLe 23 (0), .branchGe 9 (1)]

def plane489GenLeaf0034Mult : Fin 32 → Nat := ![15, 16, 16, 9, 8, 6, 2, 21, 4, 1, 9, 10, 4, 6, 4, 1, 8, 3, 8, 4, 1, 1, 7, 3, 24, 48, 23, 4, 16, 9, 11, 79]

theorem plane489GenLeaf0034 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0034Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0034Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0034Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0034Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 96
  · exact hroot.hOcc 102
  · exact hroot.hOcc 105
  · exact hroot.hOcc 121
  · exact hroot.hOcc 128
  · exact hroot.hOcc 130
  · exact hroot.hOcc 138
  · exact hroot.hOcc 139
  · exact hroot.hOcc 165
  · exact hroot.hOcc 182
  · exact hroot.hOcc 184
  · exact hroot.hOcc 191
  · exact hroot.hOcc 202
  · exact hroot.hOcc 209
  · exact hroot.hOcc 263
  · exact hroot.hOcc 283
  · exact hroot.hOcc 299
  · exact hroot.hOcc 307
  · exact hroot.hOcc 336
  · exact hroot.hOcc 342
  · exact hroot.hOcc 346
  · exact hroot.hOcc 362
  · exact hroot.hOcc 365
  · exact hroot.hOcc 369
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (26 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (7 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (18 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (31 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (23 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (9 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9

end QiushiMatmul
