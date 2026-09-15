import QiushiPlane486GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane486GenLeaf0003Refs : Fin 42 → RowRef 262 41 := ![.occ 90, .occ 91, .occ 105, .occ 114, .occ 119, .occ 121, .occ 123, .occ 127, .occ 128, .occ 129, .occ 133, .occ 135, .occ 137, .occ 146, .occ 154, .occ 161, .occ 166, .occ 174, .occ 175, .occ 177, .occ 178, .occ 179, .occ 191, .occ 194, .occ 222, .occ 230, .occ 231, .occ 234, .occ 238, .occ 240, .occ 241, .occ 243, .occ 245, .sumGe, .nonneg 0, .nonneg 38, .branchLe 22 (0), .branchGe 21 (1), .branchLe 17 (0), .branchLe 37 (0), .branchLe 4 (0), .branchLe 16 (0)]

def plane486GenLeaf0003Mult : Fin 42 → Nat := ![32083, 21122, 38038, 10434, 21810, 12178, 20515, 16760, 11470, 5787, 59763, 11192, 28245, 44770, 37284, 20023, 37949, 5727, 8427, 18336, 20027, 25754, 5810, 28039, 7894, 2976, 16708, 24206, 12855, 36372, 17234, 7669, 4522, 117388, 134598, 5087, 30781, 205791, 72435, 45447, 35078, 73159]

theorem plane486GenLeaf0003 (x : Fin 41 → Int)
    (hroot : plane486GenOccSys.RootHolds x)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane486GenLeaf0003Refs i).resolveCoeff plane486GenOccSys j)
    (fun i => (plane486GenLeaf0003Refs i).resolveRhs plane486GenOccSys) plane486GenLeaf0003Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane486GenLeaf0003Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 90
  · exact hroot.hOcc 91
  · exact hroot.hOcc 105
  · exact hroot.hOcc 114
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 123
  · exact hroot.hOcc 127
  · exact hroot.hOcc 128
  · exact hroot.hOcc 129
  · exact hroot.hOcc 133
  · exact hroot.hOcc 135
  · exact hroot.hOcc 137
  · exact hroot.hOcc 146
  · exact hroot.hOcc 154
  · exact hroot.hOcc 161
  · exact hroot.hOcc 166
  · exact hroot.hOcc 174
  · exact hroot.hOcc 175
  · exact hroot.hOcc 177
  · exact hroot.hOcc 178
  · exact hroot.hOcc 179
  · exact hroot.hOcc 191
  · exact hroot.hOcc 194
  · exact hroot.hOcc 222
  · exact hroot.hOcc 230
  · exact hroot.hOcc 231
  · exact hroot.hOcc 234
  · exact hroot.hOcc 238
  · exact hroot.hOcc 240
  · exact hroot.hOcc 241
  · exact hroot.hOcc 243
  · exact hroot.hOcc 245
  · change (∑ j, (-1 : Int) * x j) ≤ -plane486GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (38 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (22 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (21 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21
  · change (∑ k, (if k = (17 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (37 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (4 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (16 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16

end QiushiMatmul
