import QiushiPlane480GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane480GenLeaf0007Refs : Fin 21 → RowRef 221 26 := ![.occ 103, .occ 105, .occ 108, .occ 110, .occ 112, .occ 119, .occ 124, .occ 135, .occ 147, .occ 163, .occ 168, .occ 186, .occ 194, .occ 212, .occ 216, .occ 217, .sumGe, .branchLe 14 (0), .branchLe 11 (0), .branchGe 10 (1), .branchLe 13 (0)]

def plane480GenLeaf0007Mult : Fin 21 → Nat := ![5, 4, 6, 3, 1, 3, 2, 3, 1, 2, 1, 2, 3, 2, 1, 3, 6, 6, 6, 6, 6]

theorem plane480GenLeaf0007 (x : Fin 26 → Int)
    (hroot : plane480GenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane480GenLeaf0007Refs i).resolveCoeff plane480GenOccSys j)
    (fun i => (plane480GenLeaf0007Refs i).resolveRhs plane480GenOccSys) plane480GenLeaf0007Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane480GenLeaf0007Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 103
  · exact hroot.hOcc 105
  · exact hroot.hOcc 108
  · exact hroot.hOcc 110
  · exact hroot.hOcc 112
  · exact hroot.hOcc 119
  · exact hroot.hOcc 124
  · exact hroot.hOcc 135
  · exact hroot.hOcc 147
  · exact hroot.hOcc 163
  · exact hroot.hOcc 168
  · exact hroot.hOcc 186
  · exact hroot.hOcc 194
  · exact hroot.hOcc 212
  · exact hroot.hOcc 216
  · exact hroot.hOcc 217
  · change (∑ j, (-1 : Int) * x j) ≤ -plane480GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (11 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (10 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10
  · change (∑ k, (if k = (13 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13

end QiushiMatmul
