import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0004Refs : Fin 32 → RowRef 371 32 := ![.occ 95, .occ 96, .occ 99, .occ 135, .occ 140, .occ 145, .occ 147, .occ 149, .occ 151, .occ 154, .occ 155, .occ 159, .occ 178, .occ 180, .occ 188, .occ 194, .occ 196, .occ 197, .occ 202, .occ 205, .occ 234, .occ 239, .occ 306, .occ 337, .occ 344, .occ 350, .occ 351, .sumGe, .branchLe 14 (0), .branchLe 9 (0), .branchLe 31 (0), .branchGe 25 (1)]

def plane489GenLeaf0004Mult : Fin 32 → Nat := ![3448, 229, 6830, 318, 831, 2518, 415, 988, 4629, 2146, 4623, 495, 1869, 2200, 4258, 1523, 128, 1052, 1386, 5321, 1008, 1691, 189, 3243, 3564, 189, 2621, 9579, 9084, 9579, 2772, 27081]

theorem plane489GenLeaf0004 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0004Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0004Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0004Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0004Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 95
  · exact hroot.hOcc 96
  · exact hroot.hOcc 99
  · exact hroot.hOcc 135
  · exact hroot.hOcc 140
  · exact hroot.hOcc 145
  · exact hroot.hOcc 147
  · exact hroot.hOcc 149
  · exact hroot.hOcc 151
  · exact hroot.hOcc 154
  · exact hroot.hOcc 155
  · exact hroot.hOcc 159
  · exact hroot.hOcc 178
  · exact hroot.hOcc 180
  · exact hroot.hOcc 188
  · exact hroot.hOcc 194
  · exact hroot.hOcc 196
  · exact hroot.hOcc 197
  · exact hroot.hOcc 202
  · exact hroot.hOcc 205
  · exact hroot.hOcc 234
  · exact hroot.hOcc 239
  · exact hroot.hOcc 306
  · exact hroot.hOcc 337
  · exact hroot.hOcc 344
  · exact hroot.hOcc 350
  · exact hroot.hOcc 351
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (9 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (31 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (25 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25

end QiushiMatmul
