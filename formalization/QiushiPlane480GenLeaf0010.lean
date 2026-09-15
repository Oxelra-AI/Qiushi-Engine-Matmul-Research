import QiushiPlane480GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane480GenLeaf0010Refs : Fin 23 → RowRef 221 26 := ![.occ 104, .occ 107, .occ 108, .occ 109, .occ 119, .occ 126, .occ 130, .occ 141, .occ 151, .occ 163, .occ 164, .occ 169, .occ 170, .occ 190, .occ 193, .occ 207, .occ 212, .occ 215, .sumGe, .branchLe 14 (0), .branchGe 11 (1), .branchLe 5 (0), .branchLe 12 (0)]

def plane480GenLeaf0010Mult : Fin 23 → Nat := ![11, 5, 16, 13, 8, 7, 1, 5, 1, 7, 1, 3, 9, 8, 10, 1, 10, 2, 20, 18, 2, 20, 20]

theorem plane480GenLeaf0010 (x : Fin 26 → Int)
    (hroot : plane480GenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane480GenLeaf0010Refs i).resolveCoeff plane480GenOccSys j)
    (fun i => (plane480GenLeaf0010Refs i).resolveRhs plane480GenOccSys) plane480GenLeaf0010Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane480GenLeaf0010Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 104
  · exact hroot.hOcc 107
  · exact hroot.hOcc 108
  · exact hroot.hOcc 109
  · exact hroot.hOcc 119
  · exact hroot.hOcc 126
  · exact hroot.hOcc 130
  · exact hroot.hOcc 141
  · exact hroot.hOcc 151
  · exact hroot.hOcc 163
  · exact hroot.hOcc 164
  · exact hroot.hOcc 169
  · exact hroot.hOcc 170
  · exact hroot.hOcc 190
  · exact hroot.hOcc 193
  · exact hroot.hOcc 207
  · exact hroot.hOcc 212
  · exact hroot.hOcc 215
  · change (∑ j, (-1 : Int) * x j) ≤ -plane480GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (11 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11
  · change (∑ k, (if k = (5 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (12 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12

end QiushiMatmul
