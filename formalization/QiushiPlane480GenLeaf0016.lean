import QiushiPlane480GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane480GenLeaf0016Refs : Fin 27 → RowRef 221 26 := ![.occ 113, .occ 118, .occ 119, .occ 122, .occ 126, .occ 129, .occ 134, .occ 136, .occ 138, .occ 142, .occ 143, .occ 153, .occ 158, .occ 169, .occ 181, .occ 183, .occ 184, .occ 190, .occ 192, .occ 208, .occ 218, .sumGe, .branchLe 14 (0), .branchGe 11 (1), .branchLe 12 (0), .branchLe 17 (0), .branchLe 10 (0)]

def plane480GenLeaf0016Mult : Fin 27 → Nat := ![2, 6, 1, 3, 4, 4, 7, 5, 5, 5, 2, 1, 3, 3, 2, 3, 1, 5, 1, 3, 5, 12, 6, 6, 12, 12, 12]

theorem plane480GenLeaf0016 (x : Fin 26 → Int)
    (hroot : plane480GenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane480GenLeaf0016Refs i).resolveCoeff plane480GenOccSys j)
    (fun i => (plane480GenLeaf0016Refs i).resolveRhs plane480GenOccSys) plane480GenLeaf0016Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane480GenLeaf0016Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 113
  · exact hroot.hOcc 118
  · exact hroot.hOcc 119
  · exact hroot.hOcc 122
  · exact hroot.hOcc 126
  · exact hroot.hOcc 129
  · exact hroot.hOcc 134
  · exact hroot.hOcc 136
  · exact hroot.hOcc 138
  · exact hroot.hOcc 142
  · exact hroot.hOcc 143
  · exact hroot.hOcc 153
  · exact hroot.hOcc 158
  · exact hroot.hOcc 169
  · exact hroot.hOcc 181
  · exact hroot.hOcc 183
  · exact hroot.hOcc 184
  · exact hroot.hOcc 190
  · exact hroot.hOcc 192
  · exact hroot.hOcc 208
  · exact hroot.hOcc 218
  · change (∑ j, (-1 : Int) * x j) ≤ -plane480GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (11 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11
  · change (∑ k, (if k = (12 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (17 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (10 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10

end QiushiMatmul
