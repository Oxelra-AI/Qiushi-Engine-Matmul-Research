import QiushiPlane480GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane480GenLeaf0023Refs : Fin 25 → RowRef 221 26 := ![.occ 101, .occ 102, .occ 105, .occ 107, .occ 109, .occ 110, .occ 112, .occ 114, .occ 117, .occ 118, .occ 133, .occ 145, .occ 163, .occ 165, .occ 195, .occ 201, .occ 209, .occ 210, .sumGe, .branchGe 6 (1), .branchLe 14 (0), .branchGe 11 (1), .branchGe 1 (1), .branchGe 12 (1), .branchGe 10 (1)]

def plane480GenLeaf0023Mult : Fin 25 → Nat := ![2, 1, 1, 2, 2, 1, 3, 4, 4, 4, 1, 4, 1, 3, 2, 2, 1, 1, 4, 1, 4, 7, 2, 9, 10]

theorem plane480GenLeaf0023 (x : Fin 26 → Int)
    (hroot : plane480GenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane480GenLeaf0023Refs i).resolveCoeff plane480GenOccSys j)
    (fun i => (plane480GenLeaf0023Refs i).resolveRhs plane480GenOccSys) plane480GenLeaf0023Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane480GenLeaf0023Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 101
  · exact hroot.hOcc 102
  · exact hroot.hOcc 105
  · exact hroot.hOcc 107
  · exact hroot.hOcc 109
  · exact hroot.hOcc 110
  · exact hroot.hOcc 112
  · exact hroot.hOcc 114
  · exact hroot.hOcc 117
  · exact hroot.hOcc 118
  · exact hroot.hOcc 133
  · exact hroot.hOcc 145
  · exact hroot.hOcc 163
  · exact hroot.hOcc 165
  · exact hroot.hOcc 195
  · exact hroot.hOcc 201
  · exact hroot.hOcc 209
  · exact hroot.hOcc 210
  · change (∑ j, (-1 : Int) * x j) ≤ -plane480GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (14 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (11 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11
  · change (∑ k, (if k = (1 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (12 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (10 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
