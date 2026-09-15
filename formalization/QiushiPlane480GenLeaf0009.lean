import QiushiPlane480GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane480GenLeaf0009Refs : Fin 26 → RowRef 221 26 := ![.occ 103, .occ 112, .occ 113, .occ 116, .occ 117, .occ 124, .occ 136, .occ 138, .occ 142, .occ 143, .occ 145, .occ 147, .occ 149, .occ 155, .occ 170, .occ 194, .occ 200, .occ 206, .occ 210, .occ 216, .sumGe, .branchLe 14 (0), .branchLe 11 (0), .branchGe 10 (1), .branchGe 13 (1), .branchGe 12 (1)]

def plane480GenLeaf0009Mult : Fin 26 → Nat := ![9, 6, 39, 7, 16, 19, 17, 8, 8, 17, 1, 18, 19, 19, 13, 5, 1, 15, 20, 3, 39, 39, 38, 23, 59, 41]

theorem plane480GenLeaf0009 (x : Fin 26 → Int)
    (hroot : plane480GenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane480GenLeaf0009Refs i).resolveCoeff plane480GenOccSys j)
    (fun i => (plane480GenLeaf0009Refs i).resolveRhs plane480GenOccSys) plane480GenLeaf0009Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane480GenLeaf0009Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 103
  · exact hroot.hOcc 112
  · exact hroot.hOcc 113
  · exact hroot.hOcc 116
  · exact hroot.hOcc 117
  · exact hroot.hOcc 124
  · exact hroot.hOcc 136
  · exact hroot.hOcc 138
  · exact hroot.hOcc 142
  · exact hroot.hOcc 143
  · exact hroot.hOcc 145
  · exact hroot.hOcc 147
  · exact hroot.hOcc 149
  · exact hroot.hOcc 155
  · exact hroot.hOcc 170
  · exact hroot.hOcc 194
  · exact hroot.hOcc 200
  · exact hroot.hOcc 206
  · exact hroot.hOcc 210
  · exact hroot.hOcc 216
  · change (∑ j, (-1 : Int) * x j) ≤ -plane480GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (11 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (10 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10
  · change (∑ k, (if k = (13 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13
  · change (∑ k, (if k = (12 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12

end QiushiMatmul
