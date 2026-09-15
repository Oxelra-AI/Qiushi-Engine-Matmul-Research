import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0006Refs : Fin 33 → RowRef 371 32 := ![.occ 96, .occ 97, .occ 100, .occ 143, .occ 148, .occ 149, .occ 161, .occ 163, .occ 178, .occ 187, .occ 197, .occ 253, .occ 277, .occ 304, .occ 307, .occ 311, .occ 322, .occ 338, .occ 339, .occ 341, .occ 344, .occ 345, .occ 348, .occ 369, .occ 370, .sumGe, .branchLe 14 (0), .branchLe 9 (0), .branchGe 31 (1), .branchLe 23 (0), .branchLe 4 (0), .branchLe 12 (0), .branchGe 22 (1)]

def plane489GenLeaf0006Mult : Fin 33 → Nat := ![227, 180, 132, 10, 58, 262, 5, 12, 210, 183, 289, 32, 70, 165, 228, 25, 159, 4, 27, 54, 23, 105, 185, 73, 258, 656, 491, 355, 257, 471, 147, 375, 1357]

theorem plane489GenLeaf0006 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0006Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0006Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0006Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0006Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 96
  · exact hroot.hOcc 97
  · exact hroot.hOcc 100
  · exact hroot.hOcc 143
  · exact hroot.hOcc 148
  · exact hroot.hOcc 149
  · exact hroot.hOcc 161
  · exact hroot.hOcc 163
  · exact hroot.hOcc 178
  · exact hroot.hOcc 187
  · exact hroot.hOcc 197
  · exact hroot.hOcc 253
  · exact hroot.hOcc 277
  · exact hroot.hOcc 304
  · exact hroot.hOcc 307
  · exact hroot.hOcc 311
  · exact hroot.hOcc 322
  · exact hroot.hOcc 338
  · exact hroot.hOcc 339
  · exact hroot.hOcc 341
  · exact hroot.hOcc 344
  · exact hroot.hOcc 345
  · exact hroot.hOcc 348
  · exact hroot.hOcc 369
  · exact hroot.hOcc 370
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (9 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (31 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (23 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (4 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (12 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (22 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22

end QiushiMatmul
