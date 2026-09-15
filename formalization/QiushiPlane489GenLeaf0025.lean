import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0025Refs : Fin 33 → RowRef 371 32 := ![.occ 95, .occ 97, .occ 104, .occ 105, .occ 106, .occ 111, .occ 112, .occ 120, .occ 133, .occ 139, .occ 157, .occ 158, .occ 165, .occ 187, .occ 199, .occ 201, .occ 202, .occ 221, .occ 291, .occ 304, .occ 308, .occ 322, .occ 326, .occ 335, .occ 342, .occ 344, .occ 360, .sumGe, .branchGe 14 (1), .branchLe 26 (0), .branchLe 7 (0), .branchLe 30 (0), .branchGe 24 (1)]

def plane489GenLeaf0025Mult : Fin 33 → Nat := ![76, 9, 63, 92, 21, 17, 17, 28, 27, 24, 3, 82, 81, 54, 39, 44, 9, 15, 42, 52, 19, 7, 37, 1, 31, 9, 21, 134, 284, 108, 116, 134, 271]

theorem plane489GenLeaf0025 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0025Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0025Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0025Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0025Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 95
  · exact hroot.hOcc 97
  · exact hroot.hOcc 104
  · exact hroot.hOcc 105
  · exact hroot.hOcc 106
  · exact hroot.hOcc 111
  · exact hroot.hOcc 112
  · exact hroot.hOcc 120
  · exact hroot.hOcc 133
  · exact hroot.hOcc 139
  · exact hroot.hOcc 157
  · exact hroot.hOcc 158
  · exact hroot.hOcc 165
  · exact hroot.hOcc 187
  · exact hroot.hOcc 199
  · exact hroot.hOcc 201
  · exact hroot.hOcc 202
  · exact hroot.hOcc 221
  · exact hroot.hOcc 291
  · exact hroot.hOcc 304
  · exact hroot.hOcc 308
  · exact hroot.hOcc 322
  · exact hroot.hOcc 326
  · exact hroot.hOcc 335
  · exact hroot.hOcc 342
  · exact hroot.hOcc 344
  · exact hroot.hOcc 360
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (26 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (7 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (30 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (24 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24

end QiushiMatmul
