import QiushiPlane480GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane480GenLeaf0025Refs : Fin 26 → RowRef 221 26 := ![.occ 103, .occ 109, .occ 111, .occ 113, .occ 116, .occ 122, .occ 123, .occ 127, .occ 131, .occ 132, .occ 133, .occ 139, .occ 143, .occ 154, .occ 157, .occ 160, .occ 166, .occ 170, .occ 173, .occ 176, .sumGe, .branchGe 14 (1), .branchLe 12 (0), .branchLe 10 (0), .branchLe 25 (0), .branchGe 13 (1)]

def plane480GenLeaf0025Mult : Fin 26 → Nat := ![2, 2, 5, 5, 3, 2, 5, 1, 3, 1, 3, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 11, 5, 5, 5, 12]

theorem plane480GenLeaf0025 (x : Fin 26 → Int)
    (hroot : plane480GenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane480GenLeaf0025Refs i).resolveCoeff plane480GenOccSys j)
    (fun i => (plane480GenLeaf0025Refs i).resolveRhs plane480GenOccSys) plane480GenLeaf0025Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane480GenLeaf0025Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 103
  · exact hroot.hOcc 109
  · exact hroot.hOcc 111
  · exact hroot.hOcc 113
  · exact hroot.hOcc 116
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 127
  · exact hroot.hOcc 131
  · exact hroot.hOcc 132
  · exact hroot.hOcc 133
  · exact hroot.hOcc 139
  · exact hroot.hOcc 143
  · exact hroot.hOcc 154
  · exact hroot.hOcc 157
  · exact hroot.hOcc 160
  · exact hroot.hOcc 166
  · exact hroot.hOcc 170
  · exact hroot.hOcc 173
  · exact hroot.hOcc 176
  · change (∑ j, (-1 : Int) * x j) ≤ -plane480GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (12 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (10 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (25 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (13 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13

end QiushiMatmul
