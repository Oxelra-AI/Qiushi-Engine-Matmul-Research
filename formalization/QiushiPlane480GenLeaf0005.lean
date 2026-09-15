import QiushiPlane480GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane480GenLeaf0005Refs : Fin 26 → RowRef 221 26 := ![.occ 108, .occ 110, .occ 113, .occ 120, .occ 121, .occ 122, .occ 125, .occ 126, .occ 128, .occ 130, .occ 135, .occ 136, .occ 140, .occ 143, .occ 150, .occ 164, .occ 170, .occ 176, .occ 183, .occ 186, .occ 192, .sumGe, .branchLe 14 (0), .branchLe 11 (0), .branchLe 10 (0), .branchLe 12 (0)]

def plane480GenLeaf0005Mult : Fin 26 → Nat := ![2, 4, 3, 2, 2, 3, 6, 6, 5, 1, 4, 2, 8, 4, 3, 5, 2, 3, 3, 5, 4, 12, 12, 12, 12, 12]

theorem plane480GenLeaf0005 (x : Fin 26 → Int)
    (hroot : plane480GenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane480GenLeaf0005Refs i).resolveCoeff plane480GenOccSys j)
    (fun i => (plane480GenLeaf0005Refs i).resolveRhs plane480GenOccSys) plane480GenLeaf0005Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane480GenLeaf0005Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 108
  · exact hroot.hOcc 110
  · exact hroot.hOcc 113
  · exact hroot.hOcc 120
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 125
  · exact hroot.hOcc 126
  · exact hroot.hOcc 128
  · exact hroot.hOcc 130
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 140
  · exact hroot.hOcc 143
  · exact hroot.hOcc 150
  · exact hroot.hOcc 164
  · exact hroot.hOcc 170
  · exact hroot.hOcc 176
  · exact hroot.hOcc 183
  · exact hroot.hOcc 186
  · exact hroot.hOcc 192
  · change (∑ j, (-1 : Int) * x j) ≤ -plane480GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (11 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (10 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (12 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12

end QiushiMatmul
