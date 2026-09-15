import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0033Refs : Fin 30 → RowRef 371 32 := ![.occ 97, .occ 98, .occ 100, .occ 105, .occ 115, .occ 133, .occ 140, .occ 149, .occ 158, .occ 165, .occ 172, .occ 179, .occ 187, .occ 208, .occ 216, .occ 218, .occ 233, .occ 265, .occ 327, .occ 344, .occ 360, .sumGe, .branchGe 14 (1), .branchLe 26 (0), .branchGe 7 (1), .branchLe 18 (0), .branchGe 31 (1), .branchLe 23 (0), .branchLe 9 (0), .branchGe 12 (1)]

def plane489GenLeaf0033Mult : Fin 30 → Nat := ![5, 2, 4, 2, 5, 4, 3, 5, 1, 2, 1, 2, 1, 4, 3, 4, 4, 2, 2, 1, 4, 9, 4, 6, 17, 9, 2, 7, 9, 21]

theorem plane489GenLeaf0033 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0033Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0033Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0033Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0033Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 97
  · exact hroot.hOcc 98
  · exact hroot.hOcc 100
  · exact hroot.hOcc 105
  · exact hroot.hOcc 115
  · exact hroot.hOcc 133
  · exact hroot.hOcc 140
  · exact hroot.hOcc 149
  · exact hroot.hOcc 158
  · exact hroot.hOcc 165
  · exact hroot.hOcc 172
  · exact hroot.hOcc 179
  · exact hroot.hOcc 187
  · exact hroot.hOcc 208
  · exact hroot.hOcc 216
  · exact hroot.hOcc 218
  · exact hroot.hOcc 233
  · exact hroot.hOcc 265
  · exact hroot.hOcc 327
  · exact hroot.hOcc 344
  · exact hroot.hOcc 360
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (26 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (7 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (18 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (31 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (23 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (9 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (12 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12

end QiushiMatmul
