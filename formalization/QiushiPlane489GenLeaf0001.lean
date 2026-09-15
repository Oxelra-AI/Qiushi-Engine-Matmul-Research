import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0001Refs : Fin 31 → RowRef 371 32 := ![.occ 95, .occ 96, .occ 97, .occ 100, .occ 102, .occ 105, .occ 122, .occ 148, .occ 149, .occ 177, .occ 187, .occ 188, .occ 194, .occ 201, .occ 207, .occ 208, .occ 236, .occ 277, .occ 281, .occ 302, .occ 306, .occ 307, .occ 350, .sumGe, .branchLe 14 (0), .branchLe 9 (0), .branchLe 31 (0), .branchLe 25 (0), .branchGe 10 (1), .branchLe 18 (0), .branchLe 16 (0)]

def plane489GenLeaf0001Mult : Fin 31 → Nat := ![4, 6, 6, 1, 4, 4, 2, 3, 1, 3, 4, 2, 2, 2, 1, 2, 1, 3, 1, 1, 3, 1, 4, 10, 7, 9, 10, 6, 10, 6, 10]

theorem plane489GenLeaf0001 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0001Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0001Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 95
  · exact hroot.hOcc 96
  · exact hroot.hOcc 97
  · exact hroot.hOcc 100
  · exact hroot.hOcc 102
  · exact hroot.hOcc 105
  · exact hroot.hOcc 122
  · exact hroot.hOcc 148
  · exact hroot.hOcc 149
  · exact hroot.hOcc 177
  · exact hroot.hOcc 187
  · exact hroot.hOcc 188
  · exact hroot.hOcc 194
  · exact hroot.hOcc 201
  · exact hroot.hOcc 207
  · exact hroot.hOcc 208
  · exact hroot.hOcc 236
  · exact hroot.hOcc 277
  · exact hroot.hOcc 281
  · exact hroot.hOcc 302
  · exact hroot.hOcc 306
  · exact hroot.hOcc 307
  · exact hroot.hOcc 350
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (9 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (31 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (25 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (10 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10
  · change (∑ k, (if k = (18 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (16 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16

end QiushiMatmul
