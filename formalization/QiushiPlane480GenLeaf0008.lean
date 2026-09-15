import QiushiPlane480GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane480GenLeaf0008Refs : Fin 25 → RowRef 221 26 := ![.occ 104, .occ 108, .occ 109, .occ 112, .occ 113, .occ 116, .occ 117, .occ 119, .occ 129, .occ 133, .occ 140, .occ 163, .occ 164, .occ 170, .occ 182, .occ 192, .occ 199, .occ 208, .occ 212, .sumGe, .branchLe 14 (0), .branchLe 11 (0), .branchGe 10 (1), .branchGe 13 (1), .branchLe 12 (0)]

def plane480GenLeaf0008Mult : Fin 25 → Nat := ![3, 3, 1, 2, 1, 3, 2, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 4, 2, 6, 4]

theorem plane480GenLeaf0008 (x : Fin 26 → Int)
    (hroot : plane480GenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane480GenLeaf0008Refs i).resolveCoeff plane480GenOccSys j)
    (fun i => (plane480GenLeaf0008Refs i).resolveRhs plane480GenOccSys) plane480GenLeaf0008Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane480GenLeaf0008Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 104
  · exact hroot.hOcc 108
  · exact hroot.hOcc 109
  · exact hroot.hOcc 112
  · exact hroot.hOcc 113
  · exact hroot.hOcc 116
  · exact hroot.hOcc 117
  · exact hroot.hOcc 119
  · exact hroot.hOcc 129
  · exact hroot.hOcc 133
  · exact hroot.hOcc 140
  · exact hroot.hOcc 163
  · exact hroot.hOcc 164
  · exact hroot.hOcc 170
  · exact hroot.hOcc 182
  · exact hroot.hOcc 192
  · exact hroot.hOcc 199
  · exact hroot.hOcc 208
  · exact hroot.hOcc 212
  · change (∑ j, (-1 : Int) * x j) ≤ -plane480GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (11 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (10 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10
  · change (∑ k, (if k = (13 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13
  · change (∑ k, (if k = (12 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12

end QiushiMatmul
