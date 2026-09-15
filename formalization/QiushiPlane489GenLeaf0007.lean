import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0007Refs : Fin 33 → RowRef 371 32 := ![.occ 95, .occ 96, .occ 97, .occ 102, .occ 105, .occ 115, .occ 118, .occ 129, .occ 140, .occ 141, .occ 163, .occ 187, .occ 197, .occ 250, .occ 286, .occ 306, .occ 322, .occ 337, .occ 338, .occ 341, .occ 344, .occ 345, .occ 368, .occ 370, .sumGe, .branchLe 14 (0), .branchLe 9 (0), .branchGe 31 (1), .branchLe 23 (0), .branchLe 4 (0), .branchGe 12 (1), .branchLe 18 (0), .branchLe 10 (0)]

def plane489GenLeaf0007Mult : Fin 33 → Nat := ![5, 84, 79, 48, 59, 50, 37, 17, 29, 1, 36, 38, 21, 2, 18, 15, 31, 24, 9, 18, 48, 45, 23, 24, 133, 133, 133, 126, 86, 38, 102, 34, 118]

theorem plane489GenLeaf0007 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0007Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0007Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0007Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0007Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 95
  · exact hroot.hOcc 96
  · exact hroot.hOcc 97
  · exact hroot.hOcc 102
  · exact hroot.hOcc 105
  · exact hroot.hOcc 115
  · exact hroot.hOcc 118
  · exact hroot.hOcc 129
  · exact hroot.hOcc 140
  · exact hroot.hOcc 141
  · exact hroot.hOcc 163
  · exact hroot.hOcc 187
  · exact hroot.hOcc 197
  · exact hroot.hOcc 250
  · exact hroot.hOcc 286
  · exact hroot.hOcc 306
  · exact hroot.hOcc 322
  · exact hroot.hOcc 337
  · exact hroot.hOcc 338
  · exact hroot.hOcc 341
  · exact hroot.hOcc 344
  · exact hroot.hOcc 345
  · exact hroot.hOcc 368
  · exact hroot.hOcc 370
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (9 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (31 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (23 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (4 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (12 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (18 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (10 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10

end QiushiMatmul
