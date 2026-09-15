import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0032Refs : Fin 20 → RowRef 371 32 := ![.occ 96, .occ 97, .occ 131, .occ 133, .occ 149, .occ 198, .occ 205, .occ 222, .occ 318, .occ 324, .occ 335, .occ 341, .sumGe, .branchGe 14 (1), .branchLe 26 (0), .branchGe 7 (1), .branchGe 31 (1), .branchLe 23 (0), .branchLe 9 (0), .branchLe 12 (0)]

def plane489GenLeaf0032Mult : Fin 20 → Nat := ![1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 3, 6, 3, 2, 3, 3, 3, 3]

theorem plane489GenLeaf0032 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0032Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0032Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0032Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0032Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 96
  · exact hroot.hOcc 97
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 149
  · exact hroot.hOcc 198
  · exact hroot.hOcc 205
  · exact hroot.hOcc 222
  · exact hroot.hOcc 318
  · exact hroot.hOcc 324
  · exact hroot.hOcc 335
  · exact hroot.hOcc 341
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (26 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (7 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (31 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (23 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (9 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (12 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12

end QiushiMatmul
