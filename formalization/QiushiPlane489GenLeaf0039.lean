import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0039Refs : Fin 33 → RowRef 371 32 := ![.occ 97, .occ 131, .occ 148, .occ 158, .occ 159, .occ 162, .occ 164, .occ 165, .occ 168, .occ 200, .occ 201, .occ 207, .occ 208, .occ 212, .occ 213, .occ 221, .occ 229, .occ 282, .occ 291, .occ 293, .occ 308, .occ 322, .occ 332, .occ 342, .occ 343, .occ 344, .occ 355, .sumGe, .branchGe 14 (1), .branchGe 26 (1), .branchLe 30 (0), .branchGe 13 (1), .branchGe 24 (1)]

def plane489GenLeaf0039Mult : Fin 33 → Nat := ![6, 26, 30, 62, 71, 30, 31, 24, 39, 14, 36, 7, 20, 42, 29, 26, 1, 13, 2, 19, 42, 11, 16, 30, 47, 12, 27, 116, 285, 143, 116, 161, 319]

theorem plane489GenLeaf0039 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0039Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0039Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0039Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0039Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 97
  · exact hroot.hOcc 131
  · exact hroot.hOcc 148
  · exact hroot.hOcc 158
  · exact hroot.hOcc 159
  · exact hroot.hOcc 162
  · exact hroot.hOcc 164
  · exact hroot.hOcc 165
  · exact hroot.hOcc 168
  · exact hroot.hOcc 200
  · exact hroot.hOcc 201
  · exact hroot.hOcc 207
  · exact hroot.hOcc 208
  · exact hroot.hOcc 212
  · exact hroot.hOcc 213
  · exact hroot.hOcc 221
  · exact hroot.hOcc 229
  · exact hroot.hOcc 282
  · exact hroot.hOcc 291
  · exact hroot.hOcc 293
  · exact hroot.hOcc 308
  · exact hroot.hOcc 322
  · exact hroot.hOcc 332
  · exact hroot.hOcc 342
  · exact hroot.hOcc 343
  · exact hroot.hOcc 344
  · exact hroot.hOcc 355
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (26 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (30 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (13 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13
  · change (∑ k, (if k = (24 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24

end QiushiMatmul
