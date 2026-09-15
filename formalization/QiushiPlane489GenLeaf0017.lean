import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0017Refs : Fin 33 → RowRef 371 32 := ![.occ 95, .occ 97, .occ 107, .occ 114, .occ 130, .occ 145, .occ 147, .occ 149, .occ 178, .occ 187, .occ 188, .occ 197, .occ 203, .occ 205, .occ 212, .occ 228, .occ 248, .occ 273, .occ 290, .occ 297, .occ 320, .occ 321, .occ 329, .occ 345, .occ 348, .occ 359, .occ 361, .sumGe, .branchLe 14 (0), .branchGe 9 (1), .branchLe 12 (0), .branchLe 17 (0), .branchGe 22 (1)]

def plane489GenLeaf0017Mult : Fin 33 → Nat := ![46, 64, 74, 22, 147, 35, 48, 46, 104, 110, 3, 137, 94, 2, 59, 216, 13, 41, 55, 10, 12, 76, 1, 36, 68, 58, 24, 275, 210, 488, 187, 181, 802]

theorem plane489GenLeaf0017 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0017Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0017Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0017Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0017Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 95
  · exact hroot.hOcc 97
  · exact hroot.hOcc 107
  · exact hroot.hOcc 114
  · exact hroot.hOcc 130
  · exact hroot.hOcc 145
  · exact hroot.hOcc 147
  · exact hroot.hOcc 149
  · exact hroot.hOcc 178
  · exact hroot.hOcc 187
  · exact hroot.hOcc 188
  · exact hroot.hOcc 197
  · exact hroot.hOcc 203
  · exact hroot.hOcc 205
  · exact hroot.hOcc 212
  · exact hroot.hOcc 228
  · exact hroot.hOcc 248
  · exact hroot.hOcc 273
  · exact hroot.hOcc 290
  · exact hroot.hOcc 297
  · exact hroot.hOcc 320
  · exact hroot.hOcc 321
  · exact hroot.hOcc 329
  · exact hroot.hOcc 345
  · exact hroot.hOcc 348
  · exact hroot.hOcc 359
  · exact hroot.hOcc 361
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (9 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9
  · change (∑ k, (if k = (12 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (17 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (22 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22

end QiushiMatmul
