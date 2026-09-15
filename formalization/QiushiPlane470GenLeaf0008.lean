import QiushiPlane470GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane470GenLeaf0008Refs : Fin 64 → RowRef 232 63 := ![.occ 5, .occ 10, .occ 11, .occ 12, .occ 17, .occ 20, .occ 41, .occ 48, .occ 53, .occ 58, .occ 70, .occ 72, .occ 74, .occ 75, .occ 77, .occ 84, .occ 88, .occ 99, .occ 101, .occ 103, .occ 106, .occ 107, .occ 112, .occ 114, .occ 118, .occ 126, .occ 130, .occ 132, .occ 135, .occ 139, .occ 151, .occ 152, .occ 158, .occ 163, .occ 175, .occ 185, .occ 193, .occ 194, .occ 195, .occ 208, .occ 210, .occ 216, .occ 219, .occ 220, .occ 223, .sumGe, .nonneg 3, .nonneg 16, .nonneg 21, .nonneg 24, .nonneg 32, .nonneg 35, .nonneg 38, .nonneg 42, .nonneg 45, .nonneg 48, .nonneg 50, .nonneg 51, .nonneg 52, .nonneg 54, .nonneg 55, .nonneg 61, .branchGe 12 (1), .branchGe 18 (1)]

def plane470GenLeaf0008Mult : Fin 64 → Nat := ![25631, 18975, 34950, 3844, 45150, 104, 18600, 54914, 5714, 41454, 34637, 7894, 54592, 43875, 8283, 13814, 54673, 48360, 5550, 5714, 3638, 25434, 9764, 2592, 20844, 206, 3844, 4712, 1354, 38974, 28158, 8100, 1458, 10463, 52533, 1077, 732, 1870, 18654, 2635, 15261, 11402, 1671, 11080, 8084, 81461, 7688, 11634, 8306, 3122, 3638, 9162, 18640, 62173, 3226, 13828, 6126, 37756, 2284, 10400, 65075, 1870, 190012, 477881]

theorem plane470GenLeaf0008 (x : Fin 63 → Int)
    (hroot : plane470GenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_18 : (1 : Int) ≤ x 18)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane470GenLeaf0008Refs i).resolveCoeff plane470GenOccSys j)
    (fun i => (plane470GenLeaf0008Refs i).resolveRhs plane470GenOccSys) plane470GenLeaf0008Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane470GenLeaf0008Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · exact hroot.hOcc 10
  · exact hroot.hOcc 11
  · exact hroot.hOcc 12
  · exact hroot.hOcc 17
  · exact hroot.hOcc 20
  · exact hroot.hOcc 41
  · exact hroot.hOcc 48
  · exact hroot.hOcc 53
  · exact hroot.hOcc 58
  · exact hroot.hOcc 70
  · exact hroot.hOcc 72
  · exact hroot.hOcc 74
  · exact hroot.hOcc 75
  · exact hroot.hOcc 77
  · exact hroot.hOcc 84
  · exact hroot.hOcc 88
  · exact hroot.hOcc 99
  · exact hroot.hOcc 101
  · exact hroot.hOcc 103
  · exact hroot.hOcc 106
  · exact hroot.hOcc 107
  · exact hroot.hOcc 112
  · exact hroot.hOcc 114
  · exact hroot.hOcc 118
  · exact hroot.hOcc 126
  · exact hroot.hOcc 130
  · exact hroot.hOcc 132
  · exact hroot.hOcc 135
  · exact hroot.hOcc 139
  · exact hroot.hOcc 151
  · exact hroot.hOcc 152
  · exact hroot.hOcc 158
  · exact hroot.hOcc 163
  · exact hroot.hOcc 175
  · exact hroot.hOcc 185
  · exact hroot.hOcc 193
  · exact hroot.hOcc 194
  · exact hroot.hOcc 195
  · exact hroot.hOcc 208
  · exact hroot.hOcc 210
  · exact hroot.hOcc 216
  · exact hroot.hOcc 219
  · exact hroot.hOcc 220
  · exact hroot.hOcc 223
  · change (∑ j, (-1 : Int) * x j) ≤ -plane470GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (16 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (21 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (24 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (32 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (35 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 35
  · change (∑ k, (if k = (38 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (42 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (45 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (48 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (50 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (51 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (52 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (54 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 54
  · change (∑ k, (if k = (55 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (61 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 61
  · change (∑ k, (if k = (12 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (18 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18

end QiushiMatmul
