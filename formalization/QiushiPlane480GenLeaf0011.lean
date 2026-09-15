import QiushiPlane480GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane480GenLeaf0011Refs : Fin 24 → RowRef 221 26 := ![.occ 115, .occ 119, .occ 124, .occ 127, .occ 128, .occ 132, .occ 137, .occ 158, .occ 162, .occ 167, .occ 168, .occ 180, .occ 184, .occ 190, .occ 207, .occ 216, .occ 218, .sumGe, .branchGe 6 (1), .branchLe 14 (0), .branchGe 11 (1), .branchLe 5 (0), .branchGe 12 (1), .branchLe 10 (0)]

def plane480GenLeaf0011Mult : Fin 24 → Nat := ![7, 3, 4, 3, 7, 6, 3, 3, 4, 2, 7, 5, 4, 6, 6, 7, 3, 16, 4, 13, 3, 16, 16, 16]

theorem plane480GenLeaf0011 (x : Fin 26 → Int)
    (hroot : plane480GenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane480GenLeaf0011Refs i).resolveCoeff plane480GenOccSys j)
    (fun i => (plane480GenLeaf0011Refs i).resolveRhs plane480GenOccSys) plane480GenLeaf0011Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane480GenLeaf0011Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 115
  · exact hroot.hOcc 119
  · exact hroot.hOcc 124
  · exact hroot.hOcc 127
  · exact hroot.hOcc 128
  · exact hroot.hOcc 132
  · exact hroot.hOcc 137
  · exact hroot.hOcc 158
  · exact hroot.hOcc 162
  · exact hroot.hOcc 167
  · exact hroot.hOcc 168
  · exact hroot.hOcc 180
  · exact hroot.hOcc 184
  · exact hroot.hOcc 190
  · exact hroot.hOcc 207
  · exact hroot.hOcc 216
  · exact hroot.hOcc 218
  · change (∑ j, (-1 : Int) * x j) ≤ -plane480GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (14 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (11 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11
  · change (∑ k, (if k = (5 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (12 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (10 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10

end QiushiMatmul
