import QiushiPlane480GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane480GenLeaf0000Refs : Fin 26 → RowRef 221 26 := ![.occ 112, .occ 113, .occ 114, .occ 115, .occ 119, .occ 123, .occ 129, .occ 130, .occ 131, .occ 132, .occ 134, .occ 163, .occ 171, .occ 186, .occ 188, .occ 189, .occ 199, .occ 200, .occ 202, .occ 204, .occ 206, .occ 218, .sumGe, .branchLe 6 (0), .branchLe 20 (0), .branchLe 11 (0)]

def plane480GenLeaf0000Mult : Fin 26 → Nat := ![1, 10, 18, 9, 9, 12, 31, 4, 14, 2, 8, 29, 11, 10, 1, 10, 10, 10, 10, 2, 1, 8, 41, 41, 40, 40]

theorem plane480GenLeaf0000 (x : Fin 26 → Int)
    (hroot : plane480GenOccSys.RootHolds x)
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane480GenLeaf0000Refs i).resolveCoeff plane480GenOccSys j)
    (fun i => (plane480GenLeaf0000Refs i).resolveRhs plane480GenOccSys) plane480GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane480GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 112
  · exact hroot.hOcc 113
  · exact hroot.hOcc 114
  · exact hroot.hOcc 115
  · exact hroot.hOcc 119
  · exact hroot.hOcc 123
  · exact hroot.hOcc 129
  · exact hroot.hOcc 130
  · exact hroot.hOcc 131
  · exact hroot.hOcc 132
  · exact hroot.hOcc 134
  · exact hroot.hOcc 163
  · exact hroot.hOcc 171
  · exact hroot.hOcc 186
  · exact hroot.hOcc 188
  · exact hroot.hOcc 189
  · exact hroot.hOcc 199
  · exact hroot.hOcc 200
  · exact hroot.hOcc 202
  · exact hroot.hOcc 204
  · exact hroot.hOcc 206
  · exact hroot.hOcc 218
  · change (∑ j, (-1 : Int) * x j) ≤ -plane480GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (20 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (11 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11

end QiushiMatmul
