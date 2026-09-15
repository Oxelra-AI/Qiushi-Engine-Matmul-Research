import QiushiPlane486GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane486GenLeaf0006Refs : Fin 42 → RowRef 262 41 := ![.occ 89, .occ 91, .occ 102, .occ 112, .occ 113, .occ 114, .occ 116, .occ 119, .occ 120, .occ 121, .occ 125, .occ 129, .occ 132, .occ 133, .occ 146, .occ 154, .occ 161, .occ 162, .occ 164, .occ 166, .occ 171, .occ 173, .occ 174, .occ 177, .occ 179, .occ 180, .occ 192, .occ 225, .occ 226, .occ 228, .occ 239, .occ 240, .occ 241, .occ 246, .sumGe, .nonneg 0, .branchLe 22 (0), .branchGe 21 (1), .branchLe 17 (0), .branchLe 37 (0), .branchGe 4 (1), .branchGe 10 (1)]

def plane486GenLeaf0006Mult : Fin 42 → Nat := ![26783, 23651, 10314, 5478, 15225, 6690, 68302, 31726, 10899, 1220, 34056, 68146, 14355, 32752, 51738, 34987, 13226, 554, 9940, 6936, 12282, 28965, 1131, 9342, 25508, 14952, 19992, 27743, 40460, 19032, 6534, 50045, 31602, 9804, 128641, 152257, 45177, 124698, 596, 84312, 89964, 318761]

theorem plane486GenLeaf0006 (x : Fin 41 → Int)
    (hroot : plane486GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane486GenLeaf0006Refs i).resolveCoeff plane486GenOccSys j)
    (fun i => (plane486GenLeaf0006Refs i).resolveRhs plane486GenOccSys) plane486GenLeaf0006Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane486GenLeaf0006Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 89
  · exact hroot.hOcc 91
  · exact hroot.hOcc 102
  · exact hroot.hOcc 112
  · exact hroot.hOcc 113
  · exact hroot.hOcc 114
  · exact hroot.hOcc 116
  · exact hroot.hOcc 119
  · exact hroot.hOcc 120
  · exact hroot.hOcc 121
  · exact hroot.hOcc 125
  · exact hroot.hOcc 129
  · exact hroot.hOcc 132
  · exact hroot.hOcc 133
  · exact hroot.hOcc 146
  · exact hroot.hOcc 154
  · exact hroot.hOcc 161
  · exact hroot.hOcc 162
  · exact hroot.hOcc 164
  · exact hroot.hOcc 166
  · exact hroot.hOcc 171
  · exact hroot.hOcc 173
  · exact hroot.hOcc 174
  · exact hroot.hOcc 177
  · exact hroot.hOcc 179
  · exact hroot.hOcc 180
  · exact hroot.hOcc 192
  · exact hroot.hOcc 225
  · exact hroot.hOcc 226
  · exact hroot.hOcc 228
  · exact hroot.hOcc 239
  · exact hroot.hOcc 240
  · exact hroot.hOcc 241
  · exact hroot.hOcc 246
  · change (∑ j, (-1 : Int) * x j) ≤ -plane486GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (22 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (21 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21
  · change (∑ k, (if k = (17 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (37 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (4 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (10 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
