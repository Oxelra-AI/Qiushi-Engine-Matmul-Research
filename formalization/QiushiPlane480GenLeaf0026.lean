import QiushiPlane480GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane480GenLeaf0026Refs : Fin 25 → RowRef 221 26 := ![.occ 108, .occ 111, .occ 119, .occ 121, .occ 123, .occ 125, .occ 126, .occ 127, .occ 129, .occ 130, .occ 135, .occ 140, .occ 153, .occ 169, .occ 189, .occ 199, .occ 202, .occ 208, .occ 213, .occ 218, .sumGe, .branchGe 14 (1), .branchLe 12 (0), .branchLe 10 (0), .branchGe 25 (1)]

def plane480GenLeaf0026Mult : Fin 25 → Nat := ![11, 16, 8, 4, 13, 15, 10, 9, 1, 2, 8, 14, 4, 6, 2, 12, 8, 10, 4, 5, 20, 28, 20, 20, 44]

theorem plane480GenLeaf0026 (x : Fin 26 → Int)
    (hroot : plane480GenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane480GenLeaf0026Refs i).resolveCoeff plane480GenOccSys j)
    (fun i => (plane480GenLeaf0026Refs i).resolveRhs plane480GenOccSys) plane480GenLeaf0026Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane480GenLeaf0026Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 108
  · exact hroot.hOcc 111
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 123
  · exact hroot.hOcc 125
  · exact hroot.hOcc 126
  · exact hroot.hOcc 127
  · exact hroot.hOcc 129
  · exact hroot.hOcc 130
  · exact hroot.hOcc 135
  · exact hroot.hOcc 140
  · exact hroot.hOcc 153
  · exact hroot.hOcc 169
  · exact hroot.hOcc 189
  · exact hroot.hOcc 199
  · exact hroot.hOcc 202
  · exact hroot.hOcc 208
  · exact hroot.hOcc 213
  · exact hroot.hOcc 218
  · change (∑ j, (-1 : Int) * x j) ≤ -plane480GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (12 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (10 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (25 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25

end QiushiMatmul
