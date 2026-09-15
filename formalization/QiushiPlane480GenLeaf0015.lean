import QiushiPlane480GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane480GenLeaf0015Refs : Fin 22 → RowRef 221 26 := ![.occ 112, .occ 114, .occ 115, .occ 116, .occ 117, .occ 118, .occ 127, .occ 137, .occ 140, .occ 141, .occ 143, .occ 147, .occ 177, .occ 190, .occ 209, .occ 210, .sumGe, .branchLe 14 (0), .branchGe 11 (1), .branchLe 1 (0), .branchGe 12 (1), .branchGe 10 (1)]

def plane480GenLeaf0015Mult : Fin 22 → Nat := ![2, 2, 3, 2, 3, 2, 2, 1, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 4, 4]

theorem plane480GenLeaf0015 (x : Fin 26 → Int)
    (hroot : plane480GenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane480GenLeaf0015Refs i).resolveCoeff plane480GenOccSys j)
    (fun i => (plane480GenLeaf0015Refs i).resolveRhs plane480GenOccSys) plane480GenLeaf0015Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane480GenLeaf0015Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 112
  · exact hroot.hOcc 114
  · exact hroot.hOcc 115
  · exact hroot.hOcc 116
  · exact hroot.hOcc 117
  · exact hroot.hOcc 118
  · exact hroot.hOcc 127
  · exact hroot.hOcc 137
  · exact hroot.hOcc 140
  · exact hroot.hOcc 141
  · exact hroot.hOcc 143
  · exact hroot.hOcc 147
  · exact hroot.hOcc 177
  · exact hroot.hOcc 190
  · exact hroot.hOcc 209
  · exact hroot.hOcc 210
  · change (∑ j, (-1 : Int) * x j) ≤ -plane480GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (11 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11
  · change (∑ k, (if k = (1 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (12 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (10 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
