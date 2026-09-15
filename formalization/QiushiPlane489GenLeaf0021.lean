import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0021Refs : Fin 31 → RowRef 371 32 := ![.occ 95, .occ 96, .occ 105, .occ 115, .occ 118, .occ 129, .occ 130, .occ 137, .occ 139, .occ 150, .occ 187, .occ 197, .occ 208, .occ 213, .occ 227, .occ 261, .occ 282, .occ 283, .occ 289, .occ 321, .occ 340, .occ 344, .occ 346, .occ 359, .sumGe, .branchLe 14 (0), .branchGe 9 (1), .branchGe 12 (1), .branchLe 5 (0), .branchLe 26 (0), .branchGe 24 (1)]

def plane489GenLeaf0021Mult : Fin 31 → Nat := ![1, 2, 6, 10, 2, 1, 7, 2, 6, 3, 5, 3, 2, 6, 7, 3, 1, 1, 3, 4, 2, 2, 1, 2, 13, 6, 23, 18, 8, 10, 14]

theorem plane489GenLeaf0021 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0021Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0021Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0021Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0021Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 95
  · exact hroot.hOcc 96
  · exact hroot.hOcc 105
  · exact hroot.hOcc 115
  · exact hroot.hOcc 118
  · exact hroot.hOcc 129
  · exact hroot.hOcc 130
  · exact hroot.hOcc 137
  · exact hroot.hOcc 139
  · exact hroot.hOcc 150
  · exact hroot.hOcc 187
  · exact hroot.hOcc 197
  · exact hroot.hOcc 208
  · exact hroot.hOcc 213
  · exact hroot.hOcc 227
  · exact hroot.hOcc 261
  · exact hroot.hOcc 282
  · exact hroot.hOcc 283
  · exact hroot.hOcc 289
  · exact hroot.hOcc 321
  · exact hroot.hOcc 340
  · exact hroot.hOcc 344
  · exact hroot.hOcc 346
  · exact hroot.hOcc 359
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (9 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9
  · change (∑ k, (if k = (12 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (5 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (26 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (24 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24

end QiushiMatmul
