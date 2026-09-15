import QiushiPlane480GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane480GenLeaf0029Refs : Fin 21 → RowRef 221 26 := ![.occ 107, .occ 108, .occ 111, .occ 114, .occ 115, .occ 119, .occ 120, .occ 123, .occ 132, .occ 135, .occ 140, .occ 141, .occ 143, .occ 172, .occ 179, .occ 206, .occ 215, .sumGe, .branchGe 14 (1), .branchGe 12 (1), .branchLe 13 (0)]

def plane480GenLeaf0029Mult : Fin 21 → Nat := ![1, 3, 3, 4, 1, 2, 2, 4, 1, 2, 1, 2, 2, 4, 2, 3, 1, 4, 10, 10, 4]

theorem plane480GenLeaf0029 (x : Fin 26 → Int)
    (hroot : plane480GenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hUB_13 : x 13 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane480GenLeaf0029Refs i).resolveCoeff plane480GenOccSys j)
    (fun i => (plane480GenLeaf0029Refs i).resolveRhs plane480GenOccSys) plane480GenLeaf0029Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane480GenLeaf0029Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 107
  · exact hroot.hOcc 108
  · exact hroot.hOcc 111
  · exact hroot.hOcc 114
  · exact hroot.hOcc 115
  · exact hroot.hOcc 119
  · exact hroot.hOcc 120
  · exact hroot.hOcc 123
  · exact hroot.hOcc 132
  · exact hroot.hOcc 135
  · exact hroot.hOcc 140
  · exact hroot.hOcc 141
  · exact hroot.hOcc 143
  · exact hroot.hOcc 172
  · exact hroot.hOcc 179
  · exact hroot.hOcc 206
  · exact hroot.hOcc 215
  · change (∑ j, (-1 : Int) * x j) ≤ -plane480GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (12 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (13 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13

end QiushiMatmul
