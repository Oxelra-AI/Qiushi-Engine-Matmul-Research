import QiushiPlane486GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane486GenLeaf0002Refs : Fin 42 → RowRef 262 41 := ![.occ 89, .occ 90, .occ 91, .occ 92, .occ 101, .occ 105, .occ 114, .occ 116, .occ 117, .occ 121, .occ 127, .occ 129, .occ 136, .occ 138, .occ 143, .occ 146, .occ 154, .occ 161, .occ 166, .occ 172, .occ 176, .occ 178, .occ 179, .occ 180, .occ 181, .occ 187, .occ 191, .occ 224, .occ 227, .occ 229, .occ 235, .occ 236, .occ 238, .occ 239, .occ 256, .sumGe, .nonneg 0, .nonneg 4, .nonneg 27, .branchLe 22 (0), .branchLe 21 (0), .branchGe 18 (1)]

def plane486GenLeaf0002Mult : Fin 42 → Nat := ![1483, 1734, 1131, 474, 944, 1535, 678, 505, 398, 1697, 462, 934, 2214, 338, 226, 1477, 1177, 1140, 707, 1060, 929, 162, 807, 723, 289, 134, 336, 34, 475, 764, 476, 436, 256, 1327, 546, 4190, 4617, 121, 595, 1021, 3013, 8675]

theorem plane486GenLeaf0002 (x : Fin 41 → Int)
    (hroot : plane486GenOccSys.RootHolds x)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane486GenLeaf0002Refs i).resolveCoeff plane486GenOccSys j)
    (fun i => (plane486GenLeaf0002Refs i).resolveRhs plane486GenOccSys) plane486GenLeaf0002Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane486GenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 89
  · exact hroot.hOcc 90
  · exact hroot.hOcc 91
  · exact hroot.hOcc 92
  · exact hroot.hOcc 101
  · exact hroot.hOcc 105
  · exact hroot.hOcc 114
  · exact hroot.hOcc 116
  · exact hroot.hOcc 117
  · exact hroot.hOcc 121
  · exact hroot.hOcc 127
  · exact hroot.hOcc 129
  · exact hroot.hOcc 136
  · exact hroot.hOcc 138
  · exact hroot.hOcc 143
  · exact hroot.hOcc 146
  · exact hroot.hOcc 154
  · exact hroot.hOcc 161
  · exact hroot.hOcc 166
  · exact hroot.hOcc 172
  · exact hroot.hOcc 176
  · exact hroot.hOcc 178
  · exact hroot.hOcc 179
  · exact hroot.hOcc 180
  · exact hroot.hOcc 181
  · exact hroot.hOcc 187
  · exact hroot.hOcc 191
  · exact hroot.hOcc 224
  · exact hroot.hOcc 227
  · exact hroot.hOcc 229
  · exact hroot.hOcc 235
  · exact hroot.hOcc 236
  · exact hroot.hOcc 238
  · exact hroot.hOcc 239
  · exact hroot.hOcc 256
  · change (∑ j, (-1 : Int) * x j) ≤ -plane486GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (4 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (27 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (22 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (21 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (18 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18

end QiushiMatmul
