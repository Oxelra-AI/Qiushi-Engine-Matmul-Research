import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0030Refs : Fin 33 → RowRef 371 32 := ![.occ 95, .occ 96, .occ 97, .occ 102, .occ 107, .occ 115, .occ 123, .occ 124, .occ 130, .occ 131, .occ 133, .occ 139, .occ 140, .occ 148, .occ 165, .occ 184, .occ 188, .occ 201, .occ 202, .occ 207, .occ 208, .occ 242, .occ 256, .occ 259, .occ 299, .occ 350, .sumGe, .branchGe 14 (1), .branchLe 26 (0), .branchGe 7 (1), .branchLe 18 (0), .branchLe 31 (0), .branchLe 22 (0)]

def plane489GenLeaf0030Mult : Fin 33 → Nat := ![32, 32, 23, 15, 47, 12, 26, 20, 10, 12, 15, 21, 31, 6, 29, 28, 1, 17, 6, 30, 24, 17, 12, 7, 5, 5, 64, 77, 64, 65, 59, 64, 64]

theorem plane489GenLeaf0030 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0030Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0030Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0030Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0030Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 95
  · exact hroot.hOcc 96
  · exact hroot.hOcc 97
  · exact hroot.hOcc 102
  · exact hroot.hOcc 107
  · exact hroot.hOcc 115
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 130
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 148
  · exact hroot.hOcc 165
  · exact hroot.hOcc 184
  · exact hroot.hOcc 188
  · exact hroot.hOcc 201
  · exact hroot.hOcc 202
  · exact hroot.hOcc 207
  · exact hroot.hOcc 208
  · exact hroot.hOcc 242
  · exact hroot.hOcc 256
  · exact hroot.hOcc 259
  · exact hroot.hOcc 299
  · exact hroot.hOcc 350
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (26 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (7 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (18 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (31 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (22 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22

end QiushiMatmul
