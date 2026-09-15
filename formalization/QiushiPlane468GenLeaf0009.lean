import QiushiPlane468GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane468GenLeaf0009Refs : Fin 62 → RowRef 253 62 := ![.occ 2, .occ 4, .occ 5, .occ 10, .occ 15, .occ 17, .occ 55, .occ 57, .occ 59, .occ 66, .occ 67, .occ 79, .occ 92, .occ 93, .occ 99, .occ 103, .occ 106, .occ 107, .occ 116, .occ 121, .occ 124, .occ 135, .occ 136, .occ 137, .occ 145, .occ 146, .occ 147, .occ 149, .occ 158, .occ 167, .occ 177, .occ 183, .occ 187, .occ 193, .occ 197, .occ 208, .occ 232, .occ 245, .occ 246, .occ 247, .sumGe, .nonneg 7, .nonneg 8, .nonneg 10, .nonneg 20, .nonneg 30, .nonneg 32, .nonneg 39, .nonneg 42, .nonneg 44, .nonneg 46, .nonneg 53, .nonneg 54, .nonneg 56, .nonneg 59, .nonneg 60, .branchLe 28 (0), .branchGe 51 (1), .branchLe 15 (0), .branchGe 2 (1), .branchGe 1 (1), .branchGe 11 (1)]

def plane468GenLeaf0009Mult : Fin 62 → Nat := ![2122, 2101, 917, 5075, 1887, 4659, 2718, 428, 2057, 10076, 2436, 6244, 2319, 131, 2529, 1208, 6888, 2878, 10, 6147, 1800, 3914, 1034, 1429, 1439, 3759, 667, 124, 278, 4616, 495, 1660, 1446, 1688, 3074, 1243, 15, 242, 3434, 441, 10076, 8485, 4929, 10450, 5045, 1661, 6611, 2705, 2821, 7612, 905, 2767, 910, 1468, 1825, 581, 4954, 9026, 1828, 9058, 10423, 44669]

theorem plane468GenLeaf0009 (x : Fin 62 → Int)
    (hroot : plane468GenOccSys.RootHolds x)
    (hLB_51 : (1 : Int) ≤ x 51)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane468GenLeaf0009Refs i).resolveCoeff plane468GenOccSys j)
    (fun i => (plane468GenLeaf0009Refs i).resolveRhs plane468GenOccSys) plane468GenLeaf0009Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane468GenLeaf0009Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · exact hroot.hOcc 4
  · exact hroot.hOcc 5
  · exact hroot.hOcc 10
  · exact hroot.hOcc 15
  · exact hroot.hOcc 17
  · exact hroot.hOcc 55
  · exact hroot.hOcc 57
  · exact hroot.hOcc 59
  · exact hroot.hOcc 66
  · exact hroot.hOcc 67
  · exact hroot.hOcc 79
  · exact hroot.hOcc 92
  · exact hroot.hOcc 93
  · exact hroot.hOcc 99
  · exact hroot.hOcc 103
  · exact hroot.hOcc 106
  · exact hroot.hOcc 107
  · exact hroot.hOcc 116
  · exact hroot.hOcc 121
  · exact hroot.hOcc 124
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 145
  · exact hroot.hOcc 146
  · exact hroot.hOcc 147
  · exact hroot.hOcc 149
  · exact hroot.hOcc 158
  · exact hroot.hOcc 167
  · exact hroot.hOcc 177
  · exact hroot.hOcc 183
  · exact hroot.hOcc 187
  · exact hroot.hOcc 193
  · exact hroot.hOcc 197
  · exact hroot.hOcc 208
  · exact hroot.hOcc 232
  · exact hroot.hOcc 245
  · exact hroot.hOcc 246
  · exact hroot.hOcc 247
  · change (∑ j, (-1 : Int) * x j) ≤ -plane468GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (8 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (10 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (20 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (30 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (32 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (39 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (42 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (44 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (46 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (53 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (54 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 54
  · change (∑ k, (if k = (56 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 56
  · change (∑ k, (if k = (59 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (60 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 60
  · change (∑ k, (if k = (28 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (51 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_51
  · change (∑ k, (if k = (15 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (1 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (11 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11

end QiushiMatmul
