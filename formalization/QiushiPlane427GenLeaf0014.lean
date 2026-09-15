import QiushiPlane427GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane427GenLeaf0014Refs : Fin 51 → RowRef 237 50 := ![.occ 8, .occ 15, .occ 25, .occ 29, .occ 30, .occ 36, .occ 41, .occ 45, .occ 47, .occ 55, .occ 64, .occ 66, .occ 118, .occ 130, .occ 148, .occ 149, .occ 154, .occ 157, .occ 158, .occ 161, .occ 163, .occ 166, .occ 168, .occ 177, .occ 182, .occ 189, .occ 201, .occ 204, .occ 206, .occ 210, .occ 214, .occ 225, .occ 232, .occ 233, .sumGe, .nonneg 2, .nonneg 15, .nonneg 16, .nonneg 17, .nonneg 18, .nonneg 21, .nonneg 25, .nonneg 33, .nonneg 39, .nonneg 40, .nonneg 44, .nonneg 46, .nonneg 49, .branchGe 26 (1), .branchLe 48 (0), .branchGe 35 (1)]

def plane427GenLeaf0014Mult : Fin 51 → Nat := ![3598, 324, 782, 1510, 886, 1174, 1966, 1090, 558, 2438, 638, 1414, 376, 1262, 930, 1489, 668, 633, 563, 16, 844, 1001, 441, 1297, 1192, 1403, 2145, 706, 895, 2231, 1266, 160, 1122, 1052, 5846, 1774, 966, 1638, 1074, 496, 1318, 3196, 1808, 212, 2912, 318, 1462, 1426, 7502, 2298, 6764]

theorem plane427GenLeaf0014 (x : Fin 50 → Int)
    (hroot : plane427GenOccSys.RootHolds x)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_48 : x 48 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane427GenLeaf0014Refs i).resolveCoeff plane427GenOccSys j)
    (fun i => (plane427GenLeaf0014Refs i).resolveRhs plane427GenOccSys) plane427GenLeaf0014Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane427GenLeaf0014Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 8
  · exact hroot.hOcc 15
  · exact hroot.hOcc 25
  · exact hroot.hOcc 29
  · exact hroot.hOcc 30
  · exact hroot.hOcc 36
  · exact hroot.hOcc 41
  · exact hroot.hOcc 45
  · exact hroot.hOcc 47
  · exact hroot.hOcc 55
  · exact hroot.hOcc 64
  · exact hroot.hOcc 66
  · exact hroot.hOcc 118
  · exact hroot.hOcc 130
  · exact hroot.hOcc 148
  · exact hroot.hOcc 149
  · exact hroot.hOcc 154
  · exact hroot.hOcc 157
  · exact hroot.hOcc 158
  · exact hroot.hOcc 161
  · exact hroot.hOcc 163
  · exact hroot.hOcc 166
  · exact hroot.hOcc 168
  · exact hroot.hOcc 177
  · exact hroot.hOcc 182
  · exact hroot.hOcc 189
  · exact hroot.hOcc 201
  · exact hroot.hOcc 204
  · exact hroot.hOcc 206
  · exact hroot.hOcc 210
  · exact hroot.hOcc 214
  · exact hroot.hOcc 225
  · exact hroot.hOcc 232
  · exact hroot.hOcc 233
  · change (∑ j, (-1 : Int) * x j) ≤ -plane427GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (15 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (16 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (18 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (21 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (25 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (33 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (39 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (40 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (44 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (46 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (49 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (26 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (48 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_48
  · change (∑ k, (if k = (35 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35

end QiushiMatmul
