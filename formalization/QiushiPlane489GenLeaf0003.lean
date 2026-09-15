import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0003Refs : Fin 33 → RowRef 371 32 := ![.occ 95, .occ 96, .occ 97, .occ 102, .occ 126, .occ 129, .occ 131, .occ 149, .occ 164, .occ 165, .occ 194, .occ 197, .occ 201, .occ 202, .occ 206, .occ 208, .occ 215, .occ 247, .occ 249, .occ 271, .occ 276, .occ 279, .occ 282, .occ 301, .occ 308, .occ 350, .sumGe, .branchLe 14 (0), .branchLe 9 (0), .branchLe 31 (0), .branchLe 25 (0), .branchGe 10 (1), .branchGe 18 (1)]

def plane489GenLeaf0003Mult : Fin 33 → Nat := ![334, 478, 178, 467, 412, 43, 60, 463, 57, 6, 11, 164, 111, 65, 207, 79, 142, 22, 93, 330, 174, 11, 189, 40, 40, 193, 667, 550, 478, 667, 667, 1178, 905]

theorem plane489GenLeaf0003 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0003Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0003Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0003Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0003Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 95
  · exact hroot.hOcc 96
  · exact hroot.hOcc 97
  · exact hroot.hOcc 102
  · exact hroot.hOcc 126
  · exact hroot.hOcc 129
  · exact hroot.hOcc 131
  · exact hroot.hOcc 149
  · exact hroot.hOcc 164
  · exact hroot.hOcc 165
  · exact hroot.hOcc 194
  · exact hroot.hOcc 197
  · exact hroot.hOcc 201
  · exact hroot.hOcc 202
  · exact hroot.hOcc 206
  · exact hroot.hOcc 208
  · exact hroot.hOcc 215
  · exact hroot.hOcc 247
  · exact hroot.hOcc 249
  · exact hroot.hOcc 271
  · exact hroot.hOcc 276
  · exact hroot.hOcc 279
  · exact hroot.hOcc 282
  · exact hroot.hOcc 301
  · exact hroot.hOcc 308
  · exact hroot.hOcc 350
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (9 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (31 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (25 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (10 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10
  · change (∑ k, (if k = (18 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18

end QiushiMatmul
