import QiushiPlane480GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane480GenLeaf0024Refs : Fin 23 → RowRef 221 26 := ![.occ 103, .occ 105, .occ 106, .occ 111, .occ 119, .occ 121, .occ 122, .occ 123, .occ 132, .occ 137, .occ 138, .occ 139, .occ 148, .occ 150, .occ 153, .occ 154, .occ 161, .sumGe, .branchGe 14 (1), .branchLe 12 (0), .branchLe 10 (0), .branchLe 25 (0), .branchLe 13 (0)]

def plane480GenLeaf0024Mult : Fin 23 → Nat := ![4, 1, 2, 3, 2, 2, 1, 4, 1, 3, 2, 2, 2, 3, 1, 1, 1, 4, 8, 4, 4, 4, 4]

theorem plane480GenLeaf0024 (x : Fin 26 → Int)
    (hroot : plane480GenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane480GenLeaf0024Refs i).resolveCoeff plane480GenOccSys j)
    (fun i => (plane480GenLeaf0024Refs i).resolveRhs plane480GenOccSys) plane480GenLeaf0024Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane480GenLeaf0024Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 103
  · exact hroot.hOcc 105
  · exact hroot.hOcc 106
  · exact hroot.hOcc 111
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 132
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 139
  · exact hroot.hOcc 148
  · exact hroot.hOcc 150
  · exact hroot.hOcc 153
  · exact hroot.hOcc 154
  · exact hroot.hOcc 161
  · change (∑ j, (-1 : Int) * x j) ≤ -plane480GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (12 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (10 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (25 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (13 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13

end QiushiMatmul
