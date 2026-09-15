import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0019Refs : Fin 33 → RowRef 371 32 := ![.occ 96, .occ 105, .occ 115, .occ 118, .occ 128, .occ 130, .occ 139, .occ 147, .occ 155, .occ 194, .occ 197, .occ 202, .occ 203, .occ 206, .occ 213, .occ 235, .occ 251, .occ 261, .occ 282, .occ 283, .occ 286, .occ 306, .occ 337, .occ 340, .occ 350, .occ 359, .occ 367, .occ 370, .sumGe, .branchLe 14 (0), .branchGe 9 (1), .branchGe 12 (1), .branchLe 15 (0)]

def plane489GenLeaf0019Mult : Fin 33 → Nat := ![821, 1712, 943, 1810, 2063, 886, 791, 242, 54, 439, 372, 1610, 538, 718, 235, 781, 86, 443, 610, 194, 10, 476, 47, 270, 1279, 497, 355, 500, 3479, 2139, 4000, 6945, 2869]

theorem plane489GenLeaf0019 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0019Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0019Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0019Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0019Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 96
  · exact hroot.hOcc 105
  · exact hroot.hOcc 115
  · exact hroot.hOcc 118
  · exact hroot.hOcc 128
  · exact hroot.hOcc 130
  · exact hroot.hOcc 139
  · exact hroot.hOcc 147
  · exact hroot.hOcc 155
  · exact hroot.hOcc 194
  · exact hroot.hOcc 197
  · exact hroot.hOcc 202
  · exact hroot.hOcc 203
  · exact hroot.hOcc 206
  · exact hroot.hOcc 213
  · exact hroot.hOcc 235
  · exact hroot.hOcc 251
  · exact hroot.hOcc 261
  · exact hroot.hOcc 282
  · exact hroot.hOcc 283
  · exact hroot.hOcc 286
  · exact hroot.hOcc 306
  · exact hroot.hOcc 337
  · exact hroot.hOcc 340
  · exact hroot.hOcc 350
  · exact hroot.hOcc 359
  · exact hroot.hOcc 367
  · exact hroot.hOcc 370
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (9 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9
  · change (∑ k, (if k = (12 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (15 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15

end QiushiMatmul
