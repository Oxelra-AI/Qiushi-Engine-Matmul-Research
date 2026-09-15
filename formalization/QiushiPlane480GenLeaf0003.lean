import QiushiPlane480GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane480GenLeaf0003Refs : Fin 22 → RowRef 221 26 := ![.occ 108, .occ 111, .occ 114, .occ 118, .occ 120, .occ 126, .occ 128, .occ 129, .occ 147, .occ 151, .occ 153, .occ 164, .occ 180, .occ 183, .occ 197, .occ 205, .occ 208, .sumGe, .branchLe 6 (0), .branchGe 20 (1), .branchLe 13 (0), .branchGe 11 (1)]

def plane480GenLeaf0003Mult : Fin 22 → Nat := ![1, 3, 1, 3, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 5, 5, 7, 5, 6]

theorem plane480GenLeaf0003 (x : Fin 26 → Int)
    (hroot : plane480GenOccSys.RootHolds x)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane480GenLeaf0003Refs i).resolveCoeff plane480GenOccSys j)
    (fun i => (plane480GenLeaf0003Refs i).resolveRhs plane480GenOccSys) plane480GenLeaf0003Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane480GenLeaf0003Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 108
  · exact hroot.hOcc 111
  · exact hroot.hOcc 114
  · exact hroot.hOcc 118
  · exact hroot.hOcc 120
  · exact hroot.hOcc 126
  · exact hroot.hOcc 128
  · exact hroot.hOcc 129
  · exact hroot.hOcc 147
  · exact hroot.hOcc 151
  · exact hroot.hOcc 153
  · exact hroot.hOcc 164
  · exact hroot.hOcc 180
  · exact hroot.hOcc 183
  · exact hroot.hOcc 197
  · exact hroot.hOcc 205
  · exact hroot.hOcc 208
  · change (∑ j, (-1 : Int) * x j) ≤ -plane480GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (20 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20
  · change (∑ k, (if k = (13 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (11 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11

end QiushiMatmul
