import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0040Refs : Fin 33 → RowRef 371 32 := ![.occ 100, .occ 102, .occ 137, .occ 155, .occ 159, .occ 161, .occ 164, .occ 183, .occ 194, .occ 202, .occ 205, .occ 206, .occ 207, .occ 216, .occ 268, .occ 273, .occ 277, .occ 285, .occ 287, .occ 308, .occ 315, .occ 321, .occ 322, .occ 336, .occ 337, .occ 361, .occ 366, .sumGe, .branchGe 14 (1), .branchGe 26 (1), .branchGe 30 (1), .branchLe 22 (0), .branchLe 0 (1)]

def plane489GenLeaf0040Mult : Fin 33 → Nat := ![10, 8, 525, 716, 2126, 1232, 1723, 562, 1459, 213, 276, 366, 1093, 2074, 177, 1871, 288, 541, 440, 1560, 53, 212, 2577, 767, 327, 550, 441, 4927, 2414, 12582, 461, 2529, 4927]

theorem plane489GenLeaf0040 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hUB_0 : x 0 ≤ (1 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0040Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0040Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0040Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0040Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 100
  · exact hroot.hOcc 102
  · exact hroot.hOcc 137
  · exact hroot.hOcc 155
  · exact hroot.hOcc 159
  · exact hroot.hOcc 161
  · exact hroot.hOcc 164
  · exact hroot.hOcc 183
  · exact hroot.hOcc 194
  · exact hroot.hOcc 202
  · exact hroot.hOcc 205
  · exact hroot.hOcc 206
  · exact hroot.hOcc 207
  · exact hroot.hOcc 216
  · exact hroot.hOcc 268
  · exact hroot.hOcc 273
  · exact hroot.hOcc 277
  · exact hroot.hOcc 285
  · exact hroot.hOcc 287
  · exact hroot.hOcc 308
  · exact hroot.hOcc 315
  · exact hroot.hOcc 321
  · exact hroot.hOcc 322
  · exact hroot.hOcc 336
  · exact hroot.hOcc 337
  · exact hroot.hOcc 361
  · exact hroot.hOcc 366
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (26 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (30 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (22 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (0 : Fin 32) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_0

end QiushiMatmul
