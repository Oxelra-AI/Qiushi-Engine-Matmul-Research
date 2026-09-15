import QiushiPlane425GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane425GenLeaf0001Refs : Fin 59 → RowRef 202 58 := ![.occ 26, .occ 35, .occ 36, .occ 37, .occ 38, .occ 39, .occ 44, .occ 45, .occ 50, .occ 53, .occ 65, .occ 66, .occ 68, .occ 70, .occ 71, .occ 72, .occ 77, .occ 80, .occ 88, .occ 92, .occ 94, .occ 96, .occ 109, .occ 123, .occ 126, .occ 133, .occ 137, .occ 150, .occ 152, .occ 154, .occ 156, .occ 163, .occ 177, .occ 181, .occ 187, .occ 189, .occ 191, .occ 192, .occ 193, .occ 194, .occ 198, .occ 199, .sumGe, .nonneg 2, .nonneg 3, .nonneg 13, .nonneg 14, .nonneg 15, .nonneg 21, .nonneg 22, .nonneg 23, .nonneg 38, .nonneg 41, .nonneg 45, .nonneg 55, .nonneg 56, .branchLe 17 (0), .branchLe 8 (0), .branchGe 47 (1)]

def plane425GenLeaf0001Mult : Fin 59 → Nat := ![656, 11610, 4866, 5308, 1882, 6524, 516, 3274, 212, 6224, 5502, 5396, 868, 292, 298, 1074, 146, 212, 7696, 2976, 656, 4142, 3826, 50, 4942, 3504, 1962, 350, 1350, 1308, 2614, 4136, 3388, 1468, 2158, 2708, 9155, 6671, 683, 8115, 6578, 8648, 31052, 5290, 24496, 29044, 7610, 33918, 1524, 8484, 7498, 24946, 4726, 4488, 1974, 5050, 31052, 15770, 37448]

theorem plane425GenLeaf0001 (x : Fin 58 → Int)
    (hroot : plane425GenOccSys.RootHolds x)
    (hLB_47 : (1 : Int) ≤ x 47)
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane425GenLeaf0001Refs i).resolveCoeff plane425GenOccSys j)
    (fun i => (plane425GenLeaf0001Refs i).resolveRhs plane425GenOccSys) plane425GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane425GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 26
  · exact hroot.hOcc 35
  · exact hroot.hOcc 36
  · exact hroot.hOcc 37
  · exact hroot.hOcc 38
  · exact hroot.hOcc 39
  · exact hroot.hOcc 44
  · exact hroot.hOcc 45
  · exact hroot.hOcc 50
  · exact hroot.hOcc 53
  · exact hroot.hOcc 65
  · exact hroot.hOcc 66
  · exact hroot.hOcc 68
  · exact hroot.hOcc 70
  · exact hroot.hOcc 71
  · exact hroot.hOcc 72
  · exact hroot.hOcc 77
  · exact hroot.hOcc 80
  · exact hroot.hOcc 88
  · exact hroot.hOcc 92
  · exact hroot.hOcc 94
  · exact hroot.hOcc 96
  · exact hroot.hOcc 109
  · exact hroot.hOcc 123
  · exact hroot.hOcc 126
  · exact hroot.hOcc 133
  · exact hroot.hOcc 137
  · exact hroot.hOcc 150
  · exact hroot.hOcc 152
  · exact hroot.hOcc 154
  · exact hroot.hOcc 156
  · exact hroot.hOcc 163
  · exact hroot.hOcc 177
  · exact hroot.hOcc 181
  · exact hroot.hOcc 187
  · exact hroot.hOcc 189
  · exact hroot.hOcc 191
  · exact hroot.hOcc 192
  · exact hroot.hOcc 193
  · exact hroot.hOcc 194
  · exact hroot.hOcc 198
  · exact hroot.hOcc 199
  · change (∑ j, (-1 : Int) * x j) ≤ -plane425GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (3 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (13 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (14 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (15 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (21 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (22 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (23 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (38 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (41 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (45 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (55 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (56 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 56
  · change (∑ k, (if k = (17 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (8 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (47 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_47

end QiushiMatmul
