import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0037Refs : Fin 32 → RowRef 371 32 := ![.occ 98, .occ 100, .occ 104, .occ 114, .occ 152, .occ 155, .occ 158, .occ 159, .occ 161, .occ 164, .occ 165, .occ 173, .occ 194, .occ 201, .occ 203, .occ 207, .occ 216, .occ 229, .occ 267, .occ 305, .occ 318, .occ 322, .occ 325, .occ 335, .occ 336, .occ 342, .occ 352, .sumGe, .branchGe 14 (1), .branchGe 26 (1), .branchLe 30 (0), .branchLe 13 (0)]

def plane489GenLeaf0037Mult : Fin 32 → Nat := ![15, 89, 17, 4, 7, 6, 31, 70, 21, 54, 4, 2, 13, 10, 28, 14, 39, 32, 17, 7, 8, 26, 20, 4, 24, 15, 26, 97, 117, 268, 71, 69]

theorem plane489GenLeaf0037 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0037Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0037Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0037Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0037Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 98
  · exact hroot.hOcc 100
  · exact hroot.hOcc 104
  · exact hroot.hOcc 114
  · exact hroot.hOcc 152
  · exact hroot.hOcc 155
  · exact hroot.hOcc 158
  · exact hroot.hOcc 159
  · exact hroot.hOcc 161
  · exact hroot.hOcc 164
  · exact hroot.hOcc 165
  · exact hroot.hOcc 173
  · exact hroot.hOcc 194
  · exact hroot.hOcc 201
  · exact hroot.hOcc 203
  · exact hroot.hOcc 207
  · exact hroot.hOcc 216
  · exact hroot.hOcc 229
  · exact hroot.hOcc 267
  · exact hroot.hOcc 305
  · exact hroot.hOcc 318
  · exact hroot.hOcc 322
  · exact hroot.hOcc 325
  · exact hroot.hOcc 335
  · exact hroot.hOcc 336
  · exact hroot.hOcc 342
  · exact hroot.hOcc 352
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (26 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (30 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (13 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13

end QiushiMatmul
