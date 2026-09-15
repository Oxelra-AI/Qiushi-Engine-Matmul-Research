import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0029Refs : Fin 33 → RowRef 371 32 := ![.occ 97, .occ 100, .occ 105, .occ 115, .occ 133, .occ 135, .occ 139, .occ 140, .occ 158, .occ 163, .occ 178, .occ 198, .occ 206, .occ 207, .occ 213, .occ 246, .occ 260, .occ 265, .occ 269, .occ 287, .occ 304, .occ 313, .occ 337, .occ 342, .occ 348, .occ 350, .occ 353, .sumGe, .branchGe 14 (1), .branchLe 26 (0), .branchLe 7 (0), .branchGe 30 (1), .branchGe 16 (1)]

def plane489GenLeaf0029Mult : Fin 33 → Nat := ![61, 45, 103, 56, 14, 42, 10, 17, 30, 79, 31, 10, 99, 1, 15, 18, 41, 29, 5, 19, 7, 11, 33, 33, 74, 10, 28, 151, 100, 151, 134, 252, 354]

theorem plane489GenLeaf0029 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0029Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0029Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0029Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0029Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 97
  · exact hroot.hOcc 100
  · exact hroot.hOcc 105
  · exact hroot.hOcc 115
  · exact hroot.hOcc 133
  · exact hroot.hOcc 135
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 158
  · exact hroot.hOcc 163
  · exact hroot.hOcc 178
  · exact hroot.hOcc 198
  · exact hroot.hOcc 206
  · exact hroot.hOcc 207
  · exact hroot.hOcc 213
  · exact hroot.hOcc 246
  · exact hroot.hOcc 260
  · exact hroot.hOcc 265
  · exact hroot.hOcc 269
  · exact hroot.hOcc 287
  · exact hroot.hOcc 304
  · exact hroot.hOcc 313
  · exact hroot.hOcc 337
  · exact hroot.hOcc 342
  · exact hroot.hOcc 348
  · exact hroot.hOcc 350
  · exact hroot.hOcc 353
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (26 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (7 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (30 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (16 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16

end QiushiMatmul
