import QiushiPlane480GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane480GenLeaf0020Refs : Fin 26 → RowRef 221 26 := ![.occ 101, .occ 106, .occ 108, .occ 114, .occ 118, .occ 130, .occ 132, .occ 137, .occ 139, .occ 141, .occ 144, .occ 165, .occ 168, .occ 180, .occ 186, .occ 201, .occ 208, .occ 209, .occ 216, .sumGe, .branchLe 14 (0), .branchGe 11 (1), .branchGe 12 (1), .branchLe 10 (0), .branchLe 13 (0), .branchLe 15 (0)]

def plane480GenLeaf0020Mult : Fin 26 → Nat := ![1, 3, 8, 3, 7, 3, 1, 3, 3, 2, 2, 1, 4, 4, 1, 1, 3, 3, 1, 8, 8, 4, 6, 8, 8, 8]

theorem plane480GenLeaf0020 (x : Fin 26 → Int)
    (hroot : plane480GenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane480GenLeaf0020Refs i).resolveCoeff plane480GenOccSys j)
    (fun i => (plane480GenLeaf0020Refs i).resolveRhs plane480GenOccSys) plane480GenLeaf0020Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane480GenLeaf0020Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 101
  · exact hroot.hOcc 106
  · exact hroot.hOcc 108
  · exact hroot.hOcc 114
  · exact hroot.hOcc 118
  · exact hroot.hOcc 130
  · exact hroot.hOcc 132
  · exact hroot.hOcc 137
  · exact hroot.hOcc 139
  · exact hroot.hOcc 141
  · exact hroot.hOcc 144
  · exact hroot.hOcc 165
  · exact hroot.hOcc 168
  · exact hroot.hOcc 180
  · exact hroot.hOcc 186
  · exact hroot.hOcc 201
  · exact hroot.hOcc 208
  · exact hroot.hOcc 209
  · exact hroot.hOcc 216
  · change (∑ j, (-1 : Int) * x j) ≤ -plane480GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (11 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11
  · change (∑ k, (if k = (12 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (10 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (13 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (15 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15

end QiushiMatmul
