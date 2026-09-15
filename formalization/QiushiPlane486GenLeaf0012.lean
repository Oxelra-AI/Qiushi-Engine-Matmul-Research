import QiushiPlane486GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane486GenLeaf0012Refs : Fin 42 → RowRef 262 41 := ![.occ 90, .occ 95, .occ 97, .occ 99, .occ 105, .occ 106, .occ 107, .occ 109, .occ 114, .occ 119, .occ 121, .occ 133, .occ 136, .occ 139, .occ 146, .occ 153, .occ 154, .occ 155, .occ 157, .occ 161, .occ 166, .occ 178, .occ 180, .occ 185, .occ 186, .occ 196, .occ 199, .occ 207, .occ 208, .occ 210, .occ 223, .occ 226, .occ 236, .occ 253, .occ 257, .sumGe, .nonneg 0, .nonneg 21, .branchGe 22 (1), .branchLe 16 (0), .branchGe 3 (1), .branchGe 36 (1)]

def plane486GenLeaf0012Mult : Fin 42 → Nat := ![29477, 5039, 2702, 11305, 5350, 7444, 23891, 312, 6603, 17224, 1844, 17304, 9615, 11566, 6404, 11549, 6662, 7273, 3830, 8166, 11459, 20904, 9766, 182, 12738, 3793, 5714, 6297, 7508, 7808, 6271, 1130, 18715, 978, 5726, 44386, 50440, 8827, 105115, 24223, 13604, 84873]

theorem plane486GenLeaf0012 (x : Fin 41 → Int)
    (hroot : plane486GenOccSys.RootHolds x)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hUB_16 : x 16 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane486GenLeaf0012Refs i).resolveCoeff plane486GenOccSys j)
    (fun i => (plane486GenLeaf0012Refs i).resolveRhs plane486GenOccSys) plane486GenLeaf0012Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane486GenLeaf0012Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 90
  · exact hroot.hOcc 95
  · exact hroot.hOcc 97
  · exact hroot.hOcc 99
  · exact hroot.hOcc 105
  · exact hroot.hOcc 106
  · exact hroot.hOcc 107
  · exact hroot.hOcc 109
  · exact hroot.hOcc 114
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 133
  · exact hroot.hOcc 136
  · exact hroot.hOcc 139
  · exact hroot.hOcc 146
  · exact hroot.hOcc 153
  · exact hroot.hOcc 154
  · exact hroot.hOcc 155
  · exact hroot.hOcc 157
  · exact hroot.hOcc 161
  · exact hroot.hOcc 166
  · exact hroot.hOcc 178
  · exact hroot.hOcc 180
  · exact hroot.hOcc 185
  · exact hroot.hOcc 186
  · exact hroot.hOcc 196
  · exact hroot.hOcc 199
  · exact hroot.hOcc 207
  · exact hroot.hOcc 208
  · exact hroot.hOcc 210
  · exact hroot.hOcc 223
  · exact hroot.hOcc 226
  · exact hroot.hOcc 236
  · exact hroot.hOcc 253
  · exact hroot.hOcc 257
  · change (∑ j, (-1 : Int) * x j) ≤ -plane486GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (21 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (22 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22
  · change (∑ k, (if k = (16 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (3 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3
  · change (∑ k, (if k = (36 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36

end QiushiMatmul
