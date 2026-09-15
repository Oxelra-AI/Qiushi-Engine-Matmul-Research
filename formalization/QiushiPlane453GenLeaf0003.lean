import QiushiPlane453GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane453GenLeaf0003Refs : Fin 51 → RowRef 210 50 := ![.occ 14, .occ 16, .occ 21, .occ 46, .occ 52, .occ 61, .occ 64, .occ 67, .occ 88, .occ 90, .occ 95, .occ 99, .occ 103, .occ 104, .occ 105, .occ 116, .occ 133, .occ 137, .occ 138, .occ 139, .occ 145, .occ 161, .occ 163, .occ 165, .occ 166, .occ 167, .occ 172, .occ 183, .occ 184, .occ 188, .occ 193, .occ 197, .occ 202, .occ 203, .occ 209, .sumGe, .nonneg 20, .nonneg 22, .nonneg 25, .nonneg 29, .nonneg 31, .nonneg 43, .nonneg 45, .nonneg 47, .nonneg 48, .branchLe 35 (0), .branchLe 5 (1), .branchGe 15 (1), .branchLe 1 (0), .branchLe 17 (0), .branchGe 11 (1)]

def plane453GenLeaf0003Mult : Fin 51 → Nat := ![24268, 5050, 8856, 7857, 9005, 24973, 7423, 14596, 4791, 3225, 7147, 28081, 15862, 18631, 4545, 4268, 5530, 3813, 4423, 10464, 5357, 4025, 7080, 12216, 13867, 4447, 3920, 15501, 318, 417, 8754, 6267, 4482, 2626, 4027, 45972, 4, 29480, 7525, 8747, 25498, 13373, 6548, 12185, 10361, 33054, 42052, 46421, 24692, 27623, 127067]

theorem plane453GenLeaf0003 (x : Fin 50 → Int)
    (hroot : plane453GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (1 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane453GenLeaf0003Refs i).resolveCoeff plane453GenOccSys j)
    (fun i => (plane453GenLeaf0003Refs i).resolveRhs plane453GenOccSys) plane453GenLeaf0003Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane453GenLeaf0003Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 14
  · exact hroot.hOcc 16
  · exact hroot.hOcc 21
  · exact hroot.hOcc 46
  · exact hroot.hOcc 52
  · exact hroot.hOcc 61
  · exact hroot.hOcc 64
  · exact hroot.hOcc 67
  · exact hroot.hOcc 88
  · exact hroot.hOcc 90
  · exact hroot.hOcc 95
  · exact hroot.hOcc 99
  · exact hroot.hOcc 103
  · exact hroot.hOcc 104
  · exact hroot.hOcc 105
  · exact hroot.hOcc 116
  · exact hroot.hOcc 133
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 139
  · exact hroot.hOcc 145
  · exact hroot.hOcc 161
  · exact hroot.hOcc 163
  · exact hroot.hOcc 165
  · exact hroot.hOcc 166
  · exact hroot.hOcc 167
  · exact hroot.hOcc 172
  · exact hroot.hOcc 183
  · exact hroot.hOcc 184
  · exact hroot.hOcc 188
  · exact hroot.hOcc 193
  · exact hroot.hOcc 197
  · exact hroot.hOcc 202
  · exact hroot.hOcc 203
  · exact hroot.hOcc 209
  · change (∑ j, (-1 : Int) * x j) ≤ -plane453GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (20 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (22 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (25 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (29 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (31 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 31
  · change (∑ k, (if k = (43 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 43
  · change (∑ k, (if k = (45 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (47 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (48 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (35 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (5 : Fin 50) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (15 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (1 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (17 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (11 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11

end QiushiMatmul
