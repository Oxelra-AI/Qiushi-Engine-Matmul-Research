import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0024Refs : Fin 33 → RowRef 371 32 := ![.occ 97, .occ 100, .occ 102, .occ 105, .occ 112, .occ 133, .occ 139, .occ 170, .occ 187, .occ 191, .occ 192, .occ 198, .occ 201, .occ 205, .occ 234, .occ 241, .occ 245, .occ 283, .occ 294, .occ 298, .occ 299, .occ 321, .occ 337, .occ 338, .occ 342, .occ 360, .sumGe, .branchGe 14 (1), .branchLe 26 (0), .branchLe 7 (0), .branchLe 30 (0), .branchLe 4 (0), .branchLe 24 (0)]

def plane489GenLeaf0024Mult : Fin 33 → Nat := ![787, 134, 520, 891, 238, 883, 341, 37, 292, 74, 159, 251, 433, 154, 104, 208, 14, 312, 20, 283, 11, 254, 104, 358, 58, 579, 1353, 2065, 1353, 1353, 1199, 1088, 718]

theorem plane489GenLeaf0024 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0024Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0024Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0024Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0024Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 97
  · exact hroot.hOcc 100
  · exact hroot.hOcc 102
  · exact hroot.hOcc 105
  · exact hroot.hOcc 112
  · exact hroot.hOcc 133
  · exact hroot.hOcc 139
  · exact hroot.hOcc 170
  · exact hroot.hOcc 187
  · exact hroot.hOcc 191
  · exact hroot.hOcc 192
  · exact hroot.hOcc 198
  · exact hroot.hOcc 201
  · exact hroot.hOcc 205
  · exact hroot.hOcc 234
  · exact hroot.hOcc 241
  · exact hroot.hOcc 245
  · exact hroot.hOcc 283
  · exact hroot.hOcc 294
  · exact hroot.hOcc 298
  · exact hroot.hOcc 299
  · exact hroot.hOcc 321
  · exact hroot.hOcc 337
  · exact hroot.hOcc 338
  · exact hroot.hOcc 342
  · exact hroot.hOcc 360
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (26 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (7 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (30 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (4 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (24 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24

end QiushiMatmul
