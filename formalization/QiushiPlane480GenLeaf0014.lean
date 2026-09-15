import QiushiPlane480GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane480GenLeaf0014Refs : Fin 23 → RowRef 221 26 := ![.occ 102, .occ 109, .occ 114, .occ 115, .occ 116, .occ 118, .occ 126, .occ 132, .occ 135, .occ 136, .occ 137, .occ 159, .occ 169, .occ 180, .occ 184, .occ 186, .occ 190, .occ 204, .sumGe, .branchLe 14 (0), .branchLe 1 (0), .branchGe 12 (1), .branchLe 10 (0)]

def plane480GenLeaf0014Mult : Fin 23 → Nat := ![3, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 4, 4, 4]

theorem plane480GenLeaf0014 (x : Fin 26 → Int)
    (hroot : plane480GenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane480GenLeaf0014Refs i).resolveCoeff plane480GenOccSys j)
    (fun i => (plane480GenLeaf0014Refs i).resolveRhs plane480GenOccSys) plane480GenLeaf0014Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane480GenLeaf0014Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 102
  · exact hroot.hOcc 109
  · exact hroot.hOcc 114
  · exact hroot.hOcc 115
  · exact hroot.hOcc 116
  · exact hroot.hOcc 118
  · exact hroot.hOcc 126
  · exact hroot.hOcc 132
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 159
  · exact hroot.hOcc 169
  · exact hroot.hOcc 180
  · exact hroot.hOcc 184
  · exact hroot.hOcc 186
  · exact hroot.hOcc 190
  · exact hroot.hOcc 204
  · change (∑ j, (-1 : Int) * x j) ≤ -plane480GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (12 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (10 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10

end QiushiMatmul
