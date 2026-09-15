import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0028Refs : Fin 31 → RowRef 371 32 := ![.occ 96, .occ 100, .occ 105, .occ 113, .occ 121, .occ 158, .occ 165, .occ 166, .occ 178, .occ 201, .occ 204, .occ 205, .occ 208, .occ 225, .occ 257, .occ 265, .occ 287, .occ 298, .occ 313, .occ 326, .occ 338, .occ 341, .occ 352, .occ 358, .sumGe, .branchGe 14 (1), .branchLe 26 (0), .branchLe 7 (0), .branchGe 30 (1), .branchLe 16 (0), .branchGe 28 (1)]

def plane489GenLeaf0028Mult : Fin 31 → Nat := ![9, 2, 41, 22, 2, 19, 37, 19, 37, 39, 37, 78, 16, 71, 6, 33, 48, 7, 10, 29, 6, 105, 68, 8, 152, 156, 84, 136, 351, 145, 188]

theorem plane489GenLeaf0028 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0028Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0028Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0028Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0028Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 96
  · exact hroot.hOcc 100
  · exact hroot.hOcc 105
  · exact hroot.hOcc 113
  · exact hroot.hOcc 121
  · exact hroot.hOcc 158
  · exact hroot.hOcc 165
  · exact hroot.hOcc 166
  · exact hroot.hOcc 178
  · exact hroot.hOcc 201
  · exact hroot.hOcc 204
  · exact hroot.hOcc 205
  · exact hroot.hOcc 208
  · exact hroot.hOcc 225
  · exact hroot.hOcc 257
  · exact hroot.hOcc 265
  · exact hroot.hOcc 287
  · exact hroot.hOcc 298
  · exact hroot.hOcc 313
  · exact hroot.hOcc 326
  · exact hroot.hOcc 338
  · exact hroot.hOcc 341
  · exact hroot.hOcc 352
  · exact hroot.hOcc 358
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (26 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (7 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (30 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (16 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (28 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28

end QiushiMatmul
