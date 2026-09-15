import QiushiPlane480GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane480GenLeaf0004Refs : Fin 23 → RowRef 221 26 := ![.occ 106, .occ 109, .occ 110, .occ 113, .occ 116, .occ 117, .occ 122, .occ 132, .occ 134, .occ 166, .occ 167, .occ 187, .occ 189, .occ 198, .occ 205, .occ 206, .occ 208, .occ 211, .occ 216, .sumGe, .branchLe 6 (0), .branchGe 20 (1), .branchGe 13 (1)]

def plane480GenLeaf0004Mult : Fin 23 → Nat := ![1, 4, 4, 3, 5, 9, 2, 4, 5, 9, 6, 4, 2, 2, 1, 1, 2, 5, 2, 11, 11, 20, 18]

theorem plane480GenLeaf0004 (x : Fin 26 → Int)
    (hroot : plane480GenOccSys.RootHolds x)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hUB_6 : x 6 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane480GenLeaf0004Refs i).resolveCoeff plane480GenOccSys j)
    (fun i => (plane480GenLeaf0004Refs i).resolveRhs plane480GenOccSys) plane480GenLeaf0004Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane480GenLeaf0004Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 106
  · exact hroot.hOcc 109
  · exact hroot.hOcc 110
  · exact hroot.hOcc 113
  · exact hroot.hOcc 116
  · exact hroot.hOcc 117
  · exact hroot.hOcc 122
  · exact hroot.hOcc 132
  · exact hroot.hOcc 134
  · exact hroot.hOcc 166
  · exact hroot.hOcc 167
  · exact hroot.hOcc 187
  · exact hroot.hOcc 189
  · exact hroot.hOcc 198
  · exact hroot.hOcc 205
  · exact hroot.hOcc 206
  · exact hroot.hOcc 208
  · exact hroot.hOcc 211
  · exact hroot.hOcc 216
  · change (∑ j, (-1 : Int) * x j) ≤ -plane480GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (20 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20
  · change (∑ k, (if k = (13 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13

end QiushiMatmul
