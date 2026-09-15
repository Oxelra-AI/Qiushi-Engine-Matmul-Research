import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0027Refs : Fin 22 → RowRef 371 32 := ![.occ 96, .occ 97, .occ 107, .occ 121, .occ 132, .occ 139, .occ 185, .occ 201, .occ 205, .occ 261, .occ 264, .occ 283, .occ 313, .occ 345, .occ 350, .sumGe, .branchGe 14 (1), .branchLe 26 (0), .branchLe 7 (0), .branchGe 30 (1), .branchLe 16 (0), .branchLe 28 (0)]

def plane489GenLeaf0027Mult : Fin 22 → Nat := ![2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 5, 3, 2]

theorem plane489GenLeaf0027 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0027Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0027Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0027Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0027Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 96
  · exact hroot.hOcc 97
  · exact hroot.hOcc 107
  · exact hroot.hOcc 121
  · exact hroot.hOcc 132
  · exact hroot.hOcc 139
  · exact hroot.hOcc 185
  · exact hroot.hOcc 201
  · exact hroot.hOcc 205
  · exact hroot.hOcc 261
  · exact hroot.hOcc 264
  · exact hroot.hOcc 283
  · exact hroot.hOcc 313
  · exact hroot.hOcc 345
  · exact hroot.hOcc 350
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (26 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (7 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (30 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (16 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (28 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28

end QiushiMatmul
