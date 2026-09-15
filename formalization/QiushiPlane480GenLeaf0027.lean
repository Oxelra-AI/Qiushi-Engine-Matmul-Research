import QiushiPlane480GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane480GenLeaf0027Refs : Fin 27 → RowRef 221 26 := ![.occ 106, .occ 110, .occ 111, .occ 112, .occ 117, .occ 120, .occ 121, .occ 122, .occ 123, .occ 129, .occ 130, .occ 131, .occ 137, .occ 143, .occ 152, .occ 153, .occ 178, .occ 196, .occ 202, .occ 215, .occ 217, .sumGe, .branchGe 6 (1), .branchGe 14 (1), .branchLe 12 (0), .branchGe 10 (1), .branchLe 13 (0)]

def plane480GenLeaf0027Mult : Fin 27 → Nat := ![1, 1, 1, 2, 2, 1, 4, 1, 5, 4, 2, 2, 1, 3, 3, 1, 4, 1, 1, 3, 1, 5, 5, 13, 5, 11, 5]

theorem plane480GenLeaf0027 (x : Fin 26 → Int)
    (hroot : plane480GenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane480GenLeaf0027Refs i).resolveCoeff plane480GenOccSys j)
    (fun i => (plane480GenLeaf0027Refs i).resolveRhs plane480GenOccSys) plane480GenLeaf0027Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane480GenLeaf0027Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 106
  · exact hroot.hOcc 110
  · exact hroot.hOcc 111
  · exact hroot.hOcc 112
  · exact hroot.hOcc 117
  · exact hroot.hOcc 120
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 129
  · exact hroot.hOcc 130
  · exact hroot.hOcc 131
  · exact hroot.hOcc 137
  · exact hroot.hOcc 143
  · exact hroot.hOcc 152
  · exact hroot.hOcc 153
  · exact hroot.hOcc 178
  · exact hroot.hOcc 196
  · exact hroot.hOcc 202
  · exact hroot.hOcc 215
  · exact hroot.hOcc 217
  · change (∑ j, (-1 : Int) * x j) ≤ -plane480GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (14 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (12 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (10 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10
  · change (∑ k, (if k = (13 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13

end QiushiMatmul
