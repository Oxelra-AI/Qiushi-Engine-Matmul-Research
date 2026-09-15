import QiushiPlane480GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane480GenLeaf0028Refs : Fin 22 → RowRef 221 26 := ![.occ 101, .occ 108, .occ 111, .occ 112, .occ 113, .occ 116, .occ 117, .occ 122, .occ 123, .occ 129, .occ 132, .occ 133, .occ 136, .occ 146, .occ 152, .occ 160, .occ 199, .sumGe, .branchGe 14 (1), .branchLe 12 (0), .branchGe 10 (1), .branchGe 13 (1)]

def plane480GenLeaf0028Mult : Fin 22 → Nat := ![1, 4, 1, 4, 1, 4, 4, 2, 4, 1, 1, 1, 2, 3, 2, 2, 4, 4, 8, 4, 6, 10]

theorem plane480GenLeaf0028 (x : Fin 26 → Int)
    (hroot : plane480GenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hUB_12 : x 12 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane480GenLeaf0028Refs i).resolveCoeff plane480GenOccSys j)
    (fun i => (plane480GenLeaf0028Refs i).resolveRhs plane480GenOccSys) plane480GenLeaf0028Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane480GenLeaf0028Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 101
  · exact hroot.hOcc 108
  · exact hroot.hOcc 111
  · exact hroot.hOcc 112
  · exact hroot.hOcc 113
  · exact hroot.hOcc 116
  · exact hroot.hOcc 117
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 129
  · exact hroot.hOcc 132
  · exact hroot.hOcc 133
  · exact hroot.hOcc 136
  · exact hroot.hOcc 146
  · exact hroot.hOcc 152
  · exact hroot.hOcc 160
  · exact hroot.hOcc 199
  · change (∑ j, (-1 : Int) * x j) ≤ -plane480GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (12 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (10 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10
  · change (∑ k, (if k = (13 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13

end QiushiMatmul
