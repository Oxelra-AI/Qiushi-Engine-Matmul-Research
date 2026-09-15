import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0022Refs : Fin 32 → RowRef 371 32 := ![.occ 95, .occ 100, .occ 102, .occ 105, .occ 114, .occ 139, .occ 155, .occ 159, .occ 164, .occ 171, .occ 183, .occ 193, .occ 194, .occ 195, .occ 202, .occ 208, .occ 213, .occ 216, .occ 217, .occ 224, .occ 282, .occ 306, .occ 319, .occ 337, .occ 344, .occ 345, .sumGe, .branchLe 14 (0), .branchGe 9 (1), .branchGe 12 (1), .branchLe 5 (0), .branchGe 26 (1)]

def plane489GenLeaf0022Mult : Fin 32 → Nat := ![82, 69, 15, 100, 106, 61, 43, 30, 24, 24, 62, 32, 12, 28, 1, 28, 53, 72, 52, 86, 62, 5, 58, 33, 57, 15, 163, 72, 385, 85, 163, 496]

theorem plane489GenLeaf0022 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0022Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0022Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0022Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0022Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 95
  · exact hroot.hOcc 100
  · exact hroot.hOcc 102
  · exact hroot.hOcc 105
  · exact hroot.hOcc 114
  · exact hroot.hOcc 139
  · exact hroot.hOcc 155
  · exact hroot.hOcc 159
  · exact hroot.hOcc 164
  · exact hroot.hOcc 171
  · exact hroot.hOcc 183
  · exact hroot.hOcc 193
  · exact hroot.hOcc 194
  · exact hroot.hOcc 195
  · exact hroot.hOcc 202
  · exact hroot.hOcc 208
  · exact hroot.hOcc 213
  · exact hroot.hOcc 216
  · exact hroot.hOcc 217
  · exact hroot.hOcc 224
  · exact hroot.hOcc 282
  · exact hroot.hOcc 306
  · exact hroot.hOcc 319
  · exact hroot.hOcc 337
  · exact hroot.hOcc 344
  · exact hroot.hOcc 345
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (9 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9
  · change (∑ k, (if k = (12 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (5 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (26 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26

end QiushiMatmul
