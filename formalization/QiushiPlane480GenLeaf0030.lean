import QiushiPlane480GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane480GenLeaf0030Refs : Fin 14 → RowRef 221 26 := ![.occ 105, .occ 106, .occ 111, .occ 113, .occ 114, .occ 115, .occ 116, .occ 123, .occ 203, .occ 219, .sumGe, .branchGe 14 (1), .branchGe 12 (1), .branchGe 13 (1)]

def plane480GenLeaf0030Mult : Fin 14 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2]

theorem plane480GenLeaf0030 (x : Fin 26 → Int)
    (hroot : plane480GenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_13 : (1 : Int) ≤ x 13)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane480GenLeaf0030Refs i).resolveCoeff plane480GenOccSys j)
    (fun i => (plane480GenLeaf0030Refs i).resolveRhs plane480GenOccSys) plane480GenLeaf0030Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane480GenLeaf0030Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 105
  · exact hroot.hOcc 106
  · exact hroot.hOcc 111
  · exact hroot.hOcc 113
  · exact hroot.hOcc 114
  · exact hroot.hOcc 115
  · exact hroot.hOcc 116
  · exact hroot.hOcc 123
  · exact hroot.hOcc 203
  · exact hroot.hOcc 219
  · change (∑ j, (-1 : Int) * x j) ≤ -plane480GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (12 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (13 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13

end QiushiMatmul
