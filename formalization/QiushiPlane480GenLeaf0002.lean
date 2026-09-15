import QiushiPlane480GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane480GenLeaf0002Refs : Fin 25 → RowRef 221 26 := ![.occ 105, .occ 117, .occ 119, .occ 123, .occ 126, .occ 127, .occ 128, .occ 132, .occ 143, .occ 147, .occ 148, .occ 150, .occ 156, .occ 163, .occ 164, .occ 179, .occ 186, .occ 194, .occ 204, .occ 216, .sumGe, .branchLe 6 (0), .branchGe 20 (1), .branchLe 13 (0), .branchLe 11 (0)]

def plane480GenLeaf0002Mult : Fin 25 → Nat := ![12, 10, 6, 14, 16, 1, 12, 2, 6, 1, 4, 8, 6, 10, 8, 6, 10, 3, 3, 5, 24, 24, 24, 24, 24]

theorem plane480GenLeaf0002 (x : Fin 26 → Int)
    (hroot : plane480GenOccSys.RootHolds x)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane480GenLeaf0002Refs i).resolveCoeff plane480GenOccSys j)
    (fun i => (plane480GenLeaf0002Refs i).resolveRhs plane480GenOccSys) plane480GenLeaf0002Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane480GenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 105
  · exact hroot.hOcc 117
  · exact hroot.hOcc 119
  · exact hroot.hOcc 123
  · exact hroot.hOcc 126
  · exact hroot.hOcc 127
  · exact hroot.hOcc 128
  · exact hroot.hOcc 132
  · exact hroot.hOcc 143
  · exact hroot.hOcc 147
  · exact hroot.hOcc 148
  · exact hroot.hOcc 150
  · exact hroot.hOcc 156
  · exact hroot.hOcc 163
  · exact hroot.hOcc 164
  · exact hroot.hOcc 179
  · exact hroot.hOcc 186
  · exact hroot.hOcc 194
  · exact hroot.hOcc 204
  · exact hroot.hOcc 216
  · change (∑ j, (-1 : Int) * x j) ≤ -plane480GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (20 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20
  · change (∑ k, (if k = (13 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (11 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11

end QiushiMatmul
