import QiushiPlane471GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane471GenLeaf0010Refs : Fin 64 → RowRef 304 63 := ![.occ 3, .occ 16, .occ 17, .occ 31, .occ 41, .occ 51, .occ 66, .occ 82, .occ 85, .occ 93, .occ 94, .occ 95, .occ 96, .occ 107, .occ 114, .occ 115, .occ 118, .occ 119, .occ 120, .occ 132, .occ 155, .occ 159, .occ 173, .occ 175, .occ 192, .occ 194, .occ 212, .occ 223, .occ 225, .occ 230, .occ 241, .occ 246, .occ 253, .occ 260, .occ 267, .occ 272, .occ 273, .occ 283, .occ 290, .occ 292, .occ 297, .occ 299, .sumGe, .nonneg 10, .nonneg 18, .nonneg 21, .nonneg 26, .nonneg 30, .nonneg 42, .nonneg 44, .nonneg 45, .nonneg 47, .nonneg 49, .nonneg 53, .nonneg 56, .branchLe 48 (0), .branchGe 14 (1), .branchGe 4 (1), .branchLe 8 (0), .branchLe 16 (0), .branchLe 25 (0), .branchLe 22 (0), .branchLe 38 (0), .branchGe 40 (1)]

def plane471GenLeaf0010Mult : Fin 64 → Nat := ![73687, 97371, 179890, 16483, 94682, 129471, 83196, 35741, 16411, 39039, 32262, 51127, 104345, 11377, 45986, 9492, 48065, 53612, 72178, 37805, 11788, 2906, 98397, 2400, 19008, 94926, 29306, 4312, 45820, 2765, 67128, 35538, 8008, 21012, 9181, 67775, 51430, 5609, 45030, 993, 79786, 52213, 280688, 65722, 29674, 67705, 77872, 2919, 126444, 11453, 75329, 10977, 163683, 70837, 56429, 271321, 162689, 65112, 216709, 200902, 231630, 57135, 260687, 777072]

theorem plane471GenLeaf0010 (x : Fin 63 → Int)
    (hroot : plane471GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_40 : (1 : Int) ≤ x 40)
    (hUB_48 : x 48 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_38 : x 38 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane471GenLeaf0010Refs i).resolveCoeff plane471GenOccSys j)
    (fun i => (plane471GenLeaf0010Refs i).resolveRhs plane471GenOccSys) plane471GenLeaf0010Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane471GenLeaf0010Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 3
  · exact hroot.hOcc 16
  · exact hroot.hOcc 17
  · exact hroot.hOcc 31
  · exact hroot.hOcc 41
  · exact hroot.hOcc 51
  · exact hroot.hOcc 66
  · exact hroot.hOcc 82
  · exact hroot.hOcc 85
  · exact hroot.hOcc 93
  · exact hroot.hOcc 94
  · exact hroot.hOcc 95
  · exact hroot.hOcc 96
  · exact hroot.hOcc 107
  · exact hroot.hOcc 114
  · exact hroot.hOcc 115
  · exact hroot.hOcc 118
  · exact hroot.hOcc 119
  · exact hroot.hOcc 120
  · exact hroot.hOcc 132
  · exact hroot.hOcc 155
  · exact hroot.hOcc 159
  · exact hroot.hOcc 173
  · exact hroot.hOcc 175
  · exact hroot.hOcc 192
  · exact hroot.hOcc 194
  · exact hroot.hOcc 212
  · exact hroot.hOcc 223
  · exact hroot.hOcc 225
  · exact hroot.hOcc 230
  · exact hroot.hOcc 241
  · exact hroot.hOcc 246
  · exact hroot.hOcc 253
  · exact hroot.hOcc 260
  · exact hroot.hOcc 267
  · exact hroot.hOcc 272
  · exact hroot.hOcc 273
  · exact hroot.hOcc 283
  · exact hroot.hOcc 290
  · exact hroot.hOcc 292
  · exact hroot.hOcc 297
  · exact hroot.hOcc 299
  · change (∑ j, (-1 : Int) * x j) ≤ -plane471GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (18 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (21 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (26 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (30 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (42 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (44 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (45 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (47 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (49 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (53 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (56 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 56
  · change (∑ k, (if k = (48 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_48
  · change (∑ k, (if k = (14 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (4 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (8 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (16 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (25 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (22 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (38 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (40 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_40

end QiushiMatmul
