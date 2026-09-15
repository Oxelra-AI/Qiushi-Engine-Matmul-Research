import QiushiPlane480GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane480GenLeaf0022Refs : Fin 25 → RowRef 221 26 := ![.occ 113, .occ 114, .occ 115, .occ 116, .occ 118, .occ 133, .occ 138, .occ 143, .occ 146, .occ 149, .occ 159, .occ 162, .occ 165, .occ 181, .occ 184, .occ 190, .occ 207, .occ 210, .occ 216, .sumGe, .branchLe 14 (0), .branchGe 11 (1), .branchGe 12 (1), .branchLe 10 (0), .branchGe 13 (1)]

def plane480GenLeaf0022Mult : Fin 25 → Nat := ![2, 4, 2, 2, 3, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 1, 2, 2, 2, 6, 4, 6, 10, 6, 10]

theorem plane480GenLeaf0022 (x : Fin 26 → Int)
    (hroot : plane480GenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane480GenLeaf0022Refs i).resolveCoeff plane480GenOccSys j)
    (fun i => (plane480GenLeaf0022Refs i).resolveRhs plane480GenOccSys) plane480GenLeaf0022Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane480GenLeaf0022Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 113
  · exact hroot.hOcc 114
  · exact hroot.hOcc 115
  · exact hroot.hOcc 116
  · exact hroot.hOcc 118
  · exact hroot.hOcc 133
  · exact hroot.hOcc 138
  · exact hroot.hOcc 143
  · exact hroot.hOcc 146
  · exact hroot.hOcc 149
  · exact hroot.hOcc 159
  · exact hroot.hOcc 162
  · exact hroot.hOcc 165
  · exact hroot.hOcc 181
  · exact hroot.hOcc 184
  · exact hroot.hOcc 190
  · exact hroot.hOcc 207
  · exact hroot.hOcc 210
  · exact hroot.hOcc 216
  · change (∑ j, (-1 : Int) * x j) ≤ -plane480GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (11 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11
  · change (∑ k, (if k = (12 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (10 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (13 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13

end QiushiMatmul
