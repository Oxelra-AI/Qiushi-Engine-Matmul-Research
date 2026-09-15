import QiushiPlane480GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane480GenLeaf0006Refs : Fin 27 → RowRef 221 26 := ![.occ 113, .occ 114, .occ 124, .occ 125, .occ 126, .occ 128, .occ 130, .occ 133, .occ 140, .occ 141, .occ 143, .occ 149, .occ 156, .occ 159, .occ 164, .occ 165, .occ 167, .occ 170, .occ 180, .occ 186, .occ 204, .occ 208, .sumGe, .branchLe 14 (0), .branchLe 11 (0), .branchLe 10 (0), .branchGe 12 (1)]

def plane480GenLeaf0006Mult : Fin 27 → Nat := ![11, 19, 9, 20, 17, 8, 14, 10, 24, 18, 14, 18, 12, 12, 6, 3, 16, 3, 12, 27, 4, 7, 48, 48, 48, 48, 48]

theorem plane480GenLeaf0006 (x : Fin 26 → Int)
    (hroot : plane480GenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane480GenLeaf0006Refs i).resolveCoeff plane480GenOccSys j)
    (fun i => (plane480GenLeaf0006Refs i).resolveRhs plane480GenOccSys) plane480GenLeaf0006Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane480GenLeaf0006Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 113
  · exact hroot.hOcc 114
  · exact hroot.hOcc 124
  · exact hroot.hOcc 125
  · exact hroot.hOcc 126
  · exact hroot.hOcc 128
  · exact hroot.hOcc 130
  · exact hroot.hOcc 133
  · exact hroot.hOcc 140
  · exact hroot.hOcc 141
  · exact hroot.hOcc 143
  · exact hroot.hOcc 149
  · exact hroot.hOcc 156
  · exact hroot.hOcc 159
  · exact hroot.hOcc 164
  · exact hroot.hOcc 165
  · exact hroot.hOcc 167
  · exact hroot.hOcc 170
  · exact hroot.hOcc 180
  · exact hroot.hOcc 186
  · exact hroot.hOcc 204
  · exact hroot.hOcc 208
  · change (∑ j, (-1 : Int) * x j) ≤ -plane480GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (11 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (10 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (12 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12

end QiushiMatmul
