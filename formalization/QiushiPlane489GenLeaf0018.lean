import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0018Refs : Fin 26 → RowRef 371 32 := ![.occ 95, .occ 96, .occ 99, .occ 130, .occ 135, .occ 140, .occ 141, .occ 154, .occ 158, .occ 175, .occ 182, .occ 184, .occ 193, .occ 203, .occ 211, .occ 224, .occ 238, .occ 323, .occ 338, .occ 365, .occ 369, .sumGe, .branchLe 14 (0), .branchGe 9 (1), .branchLe 12 (0), .branchGe 17 (1)]

def plane489GenLeaf0018Mult : Fin 26 → Nat := ![2, 2, 11, 2, 5, 6, 2, 4, 6, 3, 3, 7, 6, 4, 5, 2, 3, 6, 1, 1, 4, 12, 5, 28, 11, 49]

theorem plane489GenLeaf0018 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0018Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0018Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0018Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0018Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 95
  · exact hroot.hOcc 96
  · exact hroot.hOcc 99
  · exact hroot.hOcc 130
  · exact hroot.hOcc 135
  · exact hroot.hOcc 140
  · exact hroot.hOcc 141
  · exact hroot.hOcc 154
  · exact hroot.hOcc 158
  · exact hroot.hOcc 175
  · exact hroot.hOcc 182
  · exact hroot.hOcc 184
  · exact hroot.hOcc 193
  · exact hroot.hOcc 203
  · exact hroot.hOcc 211
  · exact hroot.hOcc 224
  · exact hroot.hOcc 238
  · exact hroot.hOcc 323
  · exact hroot.hOcc 338
  · exact hroot.hOcc 365
  · exact hroot.hOcc 369
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (9 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9
  · change (∑ k, (if k = (12 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (17 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17

end QiushiMatmul
