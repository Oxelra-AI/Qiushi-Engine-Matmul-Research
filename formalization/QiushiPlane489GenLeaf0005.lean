import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0005Refs : Fin 33 → RowRef 371 32 := ![.occ 101, .occ 105, .occ 131, .occ 140, .occ 148, .occ 151, .occ 161, .occ 163, .occ 164, .occ 188, .occ 206, .occ 226, .occ 238, .occ 255, .occ 258, .occ 270, .occ 322, .occ 324, .occ 338, .occ 339, .occ 340, .occ 341, .occ 345, .occ 366, .occ 369, .sumGe, .branchLe 14 (0), .branchLe 9 (0), .branchGe 31 (1), .branchLe 23 (0), .branchLe 4 (0), .branchLe 12 (0), .branchLe 22 (0)]

def plane489GenLeaf0005Mult : Fin 33 → Nat := ![269, 508, 158, 605, 168, 1080, 181, 281, 327, 539, 356, 106, 130, 5, 73, 600, 935, 271, 623, 118, 53, 651, 789, 476, 167, 2350, 1874, 2183, 1733, 2350, 434, 2297, 2183]

theorem plane489GenLeaf0005 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0005Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0005Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0005Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0005Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 101
  · exact hroot.hOcc 105
  · exact hroot.hOcc 131
  · exact hroot.hOcc 140
  · exact hroot.hOcc 148
  · exact hroot.hOcc 151
  · exact hroot.hOcc 161
  · exact hroot.hOcc 163
  · exact hroot.hOcc 164
  · exact hroot.hOcc 188
  · exact hroot.hOcc 206
  · exact hroot.hOcc 226
  · exact hroot.hOcc 238
  · exact hroot.hOcc 255
  · exact hroot.hOcc 258
  · exact hroot.hOcc 270
  · exact hroot.hOcc 322
  · exact hroot.hOcc 324
  · exact hroot.hOcc 338
  · exact hroot.hOcc 339
  · exact hroot.hOcc 340
  · exact hroot.hOcc 341
  · exact hroot.hOcc 345
  · exact hroot.hOcc 366
  · exact hroot.hOcc 369
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (9 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (31 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (23 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (4 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (12 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (22 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22

end QiushiMatmul
