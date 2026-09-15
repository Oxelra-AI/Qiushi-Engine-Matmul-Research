import QiushiPlane471GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane471GenLeaf0009Refs : Fin 64 → RowRef 304 63 := ![.occ 3, .occ 31, .occ 36, .occ 45, .occ 54, .occ 60, .occ 64, .occ 82, .occ 85, .occ 93, .occ 95, .occ 96, .occ 104, .occ 108, .occ 118, .occ 119, .occ 132, .occ 139, .occ 144, .occ 148, .occ 169, .occ 188, .occ 192, .occ 195, .occ 199, .occ 202, .occ 212, .occ 225, .occ 241, .occ 244, .occ 246, .occ 248, .occ 258, .occ 259, .occ 264, .occ 271, .occ 272, .occ 283, .occ 290, .occ 295, .occ 296, .occ 297, .occ 300, .sumGe, .nonneg 13, .nonneg 18, .nonneg 21, .nonneg 24, .nonneg 26, .nonneg 42, .nonneg 44, .nonneg 47, .nonneg 50, .nonneg 55, .nonneg 61, .branchLe 48 (0), .branchGe 14 (1), .branchGe 4 (1), .branchLe 8 (0), .branchLe 16 (0), .branchLe 25 (0), .branchLe 22 (0), .branchLe 38 (0), .branchLe 40 (0)]

def plane471GenLeaf0009Mult : Fin 64 → Nat := ![167906, 369183, 92307, 44150, 301935, 91639, 120547, 209966, 366960, 231579, 129227, 449701, 272241, 93226, 55154, 491751, 253357, 184681, 188256, 235781, 19377, 66981, 124613, 16737, 98379, 158652, 273289, 498752, 12060, 33613, 272311, 64782, 158328, 71857, 109629, 161928, 331218, 147231, 334786, 75248, 54891, 319111, 142935, 1489593, 75242, 393923, 693258, 109802, 630443, 1282940, 323432, 431543, 1150173, 437916, 161107, 1184354, 1319165, 471017, 1312649, 823677, 1184126, 1067742, 1095297, 1083174]

theorem plane471GenLeaf0009 (x : Fin 63 → Int)
    (hroot : plane471GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_48 : x 48 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane471GenLeaf0009Refs i).resolveCoeff plane471GenOccSys j)
    (fun i => (plane471GenLeaf0009Refs i).resolveRhs plane471GenOccSys) plane471GenLeaf0009Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane471GenLeaf0009Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 3
  · exact hroot.hOcc 31
  · exact hroot.hOcc 36
  · exact hroot.hOcc 45
  · exact hroot.hOcc 54
  · exact hroot.hOcc 60
  · exact hroot.hOcc 64
  · exact hroot.hOcc 82
  · exact hroot.hOcc 85
  · exact hroot.hOcc 93
  · exact hroot.hOcc 95
  · exact hroot.hOcc 96
  · exact hroot.hOcc 104
  · exact hroot.hOcc 108
  · exact hroot.hOcc 118
  · exact hroot.hOcc 119
  · exact hroot.hOcc 132
  · exact hroot.hOcc 139
  · exact hroot.hOcc 144
  · exact hroot.hOcc 148
  · exact hroot.hOcc 169
  · exact hroot.hOcc 188
  · exact hroot.hOcc 192
  · exact hroot.hOcc 195
  · exact hroot.hOcc 199
  · exact hroot.hOcc 202
  · exact hroot.hOcc 212
  · exact hroot.hOcc 225
  · exact hroot.hOcc 241
  · exact hroot.hOcc 244
  · exact hroot.hOcc 246
  · exact hroot.hOcc 248
  · exact hroot.hOcc 258
  · exact hroot.hOcc 259
  · exact hroot.hOcc 264
  · exact hroot.hOcc 271
  · exact hroot.hOcc 272
  · exact hroot.hOcc 283
  · exact hroot.hOcc 290
  · exact hroot.hOcc 295
  · exact hroot.hOcc 296
  · exact hroot.hOcc 297
  · exact hroot.hOcc 300
  · change (∑ j, (-1 : Int) * x j) ≤ -plane471GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (13 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (18 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (21 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (24 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (26 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (42 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (44 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (47 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (50 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (55 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (61 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 61
  · change (∑ k, (if k = (48 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_48
  · change (∑ k, (if k = (14 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (4 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (8 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (16 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (25 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (22 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (38 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (40 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40

end QiushiMatmul
