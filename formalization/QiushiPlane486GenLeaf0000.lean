import QiushiPlane486GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane486GenLeaf0000Refs : Fin 42 → RowRef 262 41 := ![.occ 90, .occ 91, .occ 96, .occ 105, .occ 114, .occ 115, .occ 116, .occ 121, .occ 123, .occ 127, .occ 132, .occ 133, .occ 134, .occ 136, .occ 139, .occ 147, .occ 148, .occ 154, .occ 159, .occ 161, .occ 166, .occ 169, .occ 179, .occ 180, .occ 181, .occ 183, .occ 190, .occ 191, .occ 202, .occ 205, .occ 226, .occ 231, .occ 235, .occ 238, .occ 240, .occ 251, .sumGe, .nonneg 0, .branchLe 22 (0), .branchLe 21 (0), .branchLe 18 (0), .branchLe 31 (0)]

def plane486GenLeaf0000Mult : Fin 42 → Nat := ![137685, 15599, 41716, 81438, 65591, 10457, 97703, 10415, 36742, 78393, 44474, 32363, 75955, 39557, 22326, 14534, 37636, 90964, 5828, 106380, 77184, 12452, 92824, 60160, 30003, 20549, 7520, 44563, 13178, 7818, 49691, 32718, 30325, 13524, 18705, 18210, 266804, 343836, 253626, 92054, 216832, 189620]

theorem plane486GenLeaf0000 (x : Fin 41 → Int)
    (hroot : plane486GenOccSys.RootHolds x)
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane486GenLeaf0000Refs i).resolveCoeff plane486GenOccSys j)
    (fun i => (plane486GenLeaf0000Refs i).resolveRhs plane486GenOccSys) plane486GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane486GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 90
  · exact hroot.hOcc 91
  · exact hroot.hOcc 96
  · exact hroot.hOcc 105
  · exact hroot.hOcc 114
  · exact hroot.hOcc 115
  · exact hroot.hOcc 116
  · exact hroot.hOcc 121
  · exact hroot.hOcc 123
  · exact hroot.hOcc 127
  · exact hroot.hOcc 132
  · exact hroot.hOcc 133
  · exact hroot.hOcc 134
  · exact hroot.hOcc 136
  · exact hroot.hOcc 139
  · exact hroot.hOcc 147
  · exact hroot.hOcc 148
  · exact hroot.hOcc 154
  · exact hroot.hOcc 159
  · exact hroot.hOcc 161
  · exact hroot.hOcc 166
  · exact hroot.hOcc 169
  · exact hroot.hOcc 179
  · exact hroot.hOcc 180
  · exact hroot.hOcc 181
  · exact hroot.hOcc 183
  · exact hroot.hOcc 190
  · exact hroot.hOcc 191
  · exact hroot.hOcc 202
  · exact hroot.hOcc 205
  · exact hroot.hOcc 226
  · exact hroot.hOcc 231
  · exact hroot.hOcc 235
  · exact hroot.hOcc 238
  · exact hroot.hOcc 240
  · exact hroot.hOcc 251
  · change (∑ j, (-1 : Int) * x j) ≤ -plane486GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (22 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (21 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (18 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (31 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31

end QiushiMatmul
