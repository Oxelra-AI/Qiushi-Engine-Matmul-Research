import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0042Refs : Fin 33 → RowRef 371 32 := ![.occ 95, .occ 96, .occ 114, .occ 121, .occ 158, .occ 159, .occ 161, .occ 164, .occ 178, .occ 183, .occ 187, .occ 194, .occ 198, .occ 201, .occ 203, .occ 214, .occ 229, .occ 253, .occ 277, .occ 285, .occ 305, .occ 314, .occ 316, .occ 331, .occ 341, .occ 342, .occ 348, .occ 359, .sumGe, .branchGe 14 (1), .branchGe 26 (1), .branchGe 30 (1), .branchGe 22 (1)]

def plane489GenLeaf0042Mult : Fin 33 → Nat := ![187, 232, 198, 3, 20, 204, 63, 110, 63, 20, 256, 78, 122, 156, 105, 71, 277, 29, 162, 41, 20, 46, 4, 92, 89, 63, 89, 3, 389, 292, 1114, 153, 1144]

theorem plane489GenLeaf0042 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hLB_26 : (1 : Int) ≤ x 26)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0042Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0042Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0042Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0042Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 95
  · exact hroot.hOcc 96
  · exact hroot.hOcc 114
  · exact hroot.hOcc 121
  · exact hroot.hOcc 158
  · exact hroot.hOcc 159
  · exact hroot.hOcc 161
  · exact hroot.hOcc 164
  · exact hroot.hOcc 178
  · exact hroot.hOcc 183
  · exact hroot.hOcc 187
  · exact hroot.hOcc 194
  · exact hroot.hOcc 198
  · exact hroot.hOcc 201
  · exact hroot.hOcc 203
  · exact hroot.hOcc 214
  · exact hroot.hOcc 229
  · exact hroot.hOcc 253
  · exact hroot.hOcc 277
  · exact hroot.hOcc 285
  · exact hroot.hOcc 305
  · exact hroot.hOcc 314
  · exact hroot.hOcc 316
  · exact hroot.hOcc 331
  · exact hroot.hOcc 341
  · exact hroot.hOcc 342
  · exact hroot.hOcc 348
  · exact hroot.hOcc 359
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (26 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (30 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (22 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22

end QiushiMatmul
