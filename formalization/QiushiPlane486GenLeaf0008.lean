import QiushiPlane486GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane486GenLeaf0008Refs : Fin 42 → RowRef 262 41 := ![.occ 91, .occ 102, .occ 105, .occ 110, .occ 114, .occ 115, .occ 116, .occ 119, .occ 121, .occ 129, .occ 133, .occ 136, .occ 141, .occ 146, .occ 154, .occ 163, .occ 164, .occ 166, .occ 170, .occ 171, .occ 175, .occ 180, .occ 181, .occ 193, .occ 197, .occ 203, .occ 218, .occ 222, .occ 225, .occ 227, .occ 232, .occ 240, .occ 248, .occ 250, .sumGe, .nonneg 0, .nonneg 8, .nonneg 28, .nonneg 36, .branchLe 22 (0), .branchGe 21 (1), .branchGe 17 (1)]

def plane486GenLeaf0008Mult : Fin 42 → Nat := ![40487, 17126, 53169, 6491, 6113, 31884, 22599, 12689, 15291, 972, 38697, 4763, 10411, 10753, 59616, 22847, 185, 12613, 293, 16771, 7168, 37818, 4031, 33198, 19892, 6204, 12448, 11917, 843, 22647, 3102, 25230, 24599, 4183, 91678, 51295, 23949, 3819, 15640, 44161, 202514, 203402]

theorem plane486GenLeaf0008 (x : Fin 41 → Int)
    (hroot : plane486GenOccSys.RootHolds x)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hUB_22 : x 22 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane486GenLeaf0008Refs i).resolveCoeff plane486GenOccSys j)
    (fun i => (plane486GenLeaf0008Refs i).resolveRhs plane486GenOccSys) plane486GenLeaf0008Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane486GenLeaf0008Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 91
  · exact hroot.hOcc 102
  · exact hroot.hOcc 105
  · exact hroot.hOcc 110
  · exact hroot.hOcc 114
  · exact hroot.hOcc 115
  · exact hroot.hOcc 116
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 129
  · exact hroot.hOcc 133
  · exact hroot.hOcc 136
  · exact hroot.hOcc 141
  · exact hroot.hOcc 146
  · exact hroot.hOcc 154
  · exact hroot.hOcc 163
  · exact hroot.hOcc 164
  · exact hroot.hOcc 166
  · exact hroot.hOcc 170
  · exact hroot.hOcc 171
  · exact hroot.hOcc 175
  · exact hroot.hOcc 180
  · exact hroot.hOcc 181
  · exact hroot.hOcc 193
  · exact hroot.hOcc 197
  · exact hroot.hOcc 203
  · exact hroot.hOcc 218
  · exact hroot.hOcc 222
  · exact hroot.hOcc 225
  · exact hroot.hOcc 227
  · exact hroot.hOcc 232
  · exact hroot.hOcc 240
  · exact hroot.hOcc 248
  · exact hroot.hOcc 250
  · change (∑ j, (-1 : Int) * x j) ≤ -plane486GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (8 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (28 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (36 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (22 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (21 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21
  · change (∑ k, (if k = (17 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17

end QiushiMatmul
