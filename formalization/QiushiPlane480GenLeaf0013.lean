import QiushiPlane480GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane480GenLeaf0013Refs : Fin 22 → RowRef 221 26 := ![.occ 112, .occ 116, .occ 118, .occ 119, .occ 130, .occ 132, .occ 133, .occ 138, .occ 140, .occ 143, .occ 169, .occ 170, .occ 188, .occ 193, .occ 205, .occ 208, .occ 212, .sumGe, .branchLe 14 (0), .branchGe 11 (1), .branchLe 1 (0), .branchLe 12 (0)]

def plane480GenLeaf0013Mult : Fin 22 → Nat := ![3, 8, 6, 7, 4, 5, 2, 2, 8, 7, 3, 1, 2, 6, 5, 3, 4, 12, 10, 2, 12, 12]

theorem plane480GenLeaf0013 (x : Fin 26 → Int)
    (hroot : plane480GenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane480GenLeaf0013Refs i).resolveCoeff plane480GenOccSys j)
    (fun i => (plane480GenLeaf0013Refs i).resolveRhs plane480GenOccSys) plane480GenLeaf0013Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane480GenLeaf0013Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 112
  · exact hroot.hOcc 116
  · exact hroot.hOcc 118
  · exact hroot.hOcc 119
  · exact hroot.hOcc 130
  · exact hroot.hOcc 132
  · exact hroot.hOcc 133
  · exact hroot.hOcc 138
  · exact hroot.hOcc 140
  · exact hroot.hOcc 143
  · exact hroot.hOcc 169
  · exact hroot.hOcc 170
  · exact hroot.hOcc 188
  · exact hroot.hOcc 193
  · exact hroot.hOcc 205
  · exact hroot.hOcc 208
  · exact hroot.hOcc 212
  · change (∑ j, (-1 : Int) * x j) ≤ -plane480GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (11 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11
  · change (∑ k, (if k = (1 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (12 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12

end QiushiMatmul
