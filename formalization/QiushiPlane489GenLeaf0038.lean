import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0038Refs : Fin 33 → RowRef 371 32 := ![.occ 95, .occ 96, .occ 112, .occ 129, .occ 131, .occ 133, .occ 148, .occ 159, .occ 161, .occ 174, .occ 198, .occ 201, .occ 203, .occ 216, .occ 229, .occ 234, .occ 267, .occ 277, .occ 278, .occ 282, .occ 322, .occ 336, .occ 337, .occ 343, .occ 345, .occ 362, .occ 363, .sumGe, .branchGe 14 (1), .branchGe 26 (1), .branchLe 30 (0), .branchGe 13 (1), .branchLe 24 (0)]

def plane489GenLeaf0038Mult : Fin 33 → Nat := ![12, 134, 18, 61, 127, 94, 61, 114, 129, 109, 130, 65, 136, 60, 12, 111, 31, 10, 109, 193, 22, 60, 166, 3, 16, 21, 122, 410, 292, 568, 241, 965, 410]

theorem plane489GenLeaf0038 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0038Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0038Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0038Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0038Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 95
  · exact hroot.hOcc 96
  · exact hroot.hOcc 112
  · exact hroot.hOcc 129
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 148
  · exact hroot.hOcc 159
  · exact hroot.hOcc 161
  · exact hroot.hOcc 174
  · exact hroot.hOcc 198
  · exact hroot.hOcc 201
  · exact hroot.hOcc 203
  · exact hroot.hOcc 216
  · exact hroot.hOcc 229
  · exact hroot.hOcc 234
  · exact hroot.hOcc 267
  · exact hroot.hOcc 277
  · exact hroot.hOcc 278
  · exact hroot.hOcc 282
  · exact hroot.hOcc 322
  · exact hroot.hOcc 336
  · exact hroot.hOcc 337
  · exact hroot.hOcc 343
  · exact hroot.hOcc 345
  · exact hroot.hOcc 362
  · exact hroot.hOcc 363
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (26 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (30 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (13 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13
  · change (∑ k, (if k = (24 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24

end QiushiMatmul
