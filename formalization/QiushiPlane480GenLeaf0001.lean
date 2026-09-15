import QiushiPlane480GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane480GenLeaf0001Refs : Fin 26 → RowRef 221 26 := ![.occ 105, .occ 111, .occ 112, .occ 115, .occ 118, .occ 120, .occ 121, .occ 124, .occ 127, .occ 129, .occ 142, .occ 145, .occ 146, .occ 149, .occ 163, .occ 164, .occ 186, .occ 190, .occ 204, .occ 210, .occ 218, .occ 220, .sumGe, .branchLe 6 (0), .branchLe 20 (0), .branchGe 11 (1)]

def plane480GenLeaf0001Mult : Fin 26 → Nat := ![12, 23, 16, 7, 12, 8, 7, 11, 10, 4, 28, 12, 11, 5, 2, 7, 5, 12, 16, 8, 6, 10, 40, 40, 40, 40]

theorem plane480GenLeaf0001 (x : Fin 26 → Int)
    (hroot : plane480GenOccSys.RootHolds x)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane480GenLeaf0001Refs i).resolveCoeff plane480GenOccSys j)
    (fun i => (plane480GenLeaf0001Refs i).resolveRhs plane480GenOccSys) plane480GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane480GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 105
  · exact hroot.hOcc 111
  · exact hroot.hOcc 112
  · exact hroot.hOcc 115
  · exact hroot.hOcc 118
  · exact hroot.hOcc 120
  · exact hroot.hOcc 121
  · exact hroot.hOcc 124
  · exact hroot.hOcc 127
  · exact hroot.hOcc 129
  · exact hroot.hOcc 142
  · exact hroot.hOcc 145
  · exact hroot.hOcc 146
  · exact hroot.hOcc 149
  · exact hroot.hOcc 163
  · exact hroot.hOcc 164
  · exact hroot.hOcc 186
  · exact hroot.hOcc 190
  · exact hroot.hOcc 204
  · exact hroot.hOcc 210
  · exact hroot.hOcc 218
  · exact hroot.hOcc 220
  · change (∑ j, (-1 : Int) * x j) ≤ -plane480GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (20 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (11 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11

end QiushiMatmul
