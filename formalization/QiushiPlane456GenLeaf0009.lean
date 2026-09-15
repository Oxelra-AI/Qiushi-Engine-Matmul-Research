import QiushiPlane456GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane456GenLeaf0009Refs : Fin 64 → RowRef 248 63 := ![.occ 6, .occ 9, .occ 10, .occ 15, .occ 36, .occ 45, .occ 47, .occ 61, .occ 71, .occ 72, .occ 74, .occ 82, .occ 83, .occ 84, .occ 85, .occ 88, .occ 91, .occ 92, .occ 95, .occ 101, .occ 114, .occ 117, .occ 123, .occ 127, .occ 129, .occ 134, .occ 140, .occ 143, .occ 150, .occ 156, .occ 162, .occ 172, .occ 174, .occ 175, .occ 207, .occ 212, .occ 213, .occ 214, .occ 217, .occ 226, .occ 233, .occ 234, .occ 235, .occ 236, .occ 240, .occ 241, .occ 246, .sumGe, .nonneg 20, .nonneg 26, .nonneg 28, .nonneg 32, .nonneg 38, .nonneg 42, .nonneg 44, .nonneg 48, .nonneg 51, .nonneg 53, .nonneg 55, .nonneg 58, .nonneg 60, .branchLe 24 (0), .branchGe 31 (1), .branchGe 6 (1)]

def plane456GenLeaf0009Mult : Fin 64 → Nat := ![68257, 30996, 61151, 27003, 33399, 23583, 15380, 7312, 52945, 5629, 27494, 26430, 13824, 824, 14230, 11395, 18314, 53020, 28321, 16719, 8980, 29055, 40157, 49737, 11779, 2253, 2165, 39850, 4689, 3618, 2894, 4339, 19297, 23202, 4418, 6073, 9136, 6575, 127, 18143, 10017, 18690, 8604, 26254, 1413, 16355, 8837, 102111, 39168, 34334, 82063, 35621, 79119, 64220, 36572, 33380, 10409, 48963, 8153, 68301, 52015, 53038, 355131, 333109]

theorem plane456GenLeaf0009 (x : Fin 63 → Int)
    (hroot : plane456GenOccSys.RootHolds x)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_24 : x 24 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane456GenLeaf0009Refs i).resolveCoeff plane456GenOccSys j)
    (fun i => (plane456GenLeaf0009Refs i).resolveRhs plane456GenOccSys) plane456GenLeaf0009Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane456GenLeaf0009Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 6
  · exact hroot.hOcc 9
  · exact hroot.hOcc 10
  · exact hroot.hOcc 15
  · exact hroot.hOcc 36
  · exact hroot.hOcc 45
  · exact hroot.hOcc 47
  · exact hroot.hOcc 61
  · exact hroot.hOcc 71
  · exact hroot.hOcc 72
  · exact hroot.hOcc 74
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · exact hroot.hOcc 84
  · exact hroot.hOcc 85
  · exact hroot.hOcc 88
  · exact hroot.hOcc 91
  · exact hroot.hOcc 92
  · exact hroot.hOcc 95
  · exact hroot.hOcc 101
  · exact hroot.hOcc 114
  · exact hroot.hOcc 117
  · exact hroot.hOcc 123
  · exact hroot.hOcc 127
  · exact hroot.hOcc 129
  · exact hroot.hOcc 134
  · exact hroot.hOcc 140
  · exact hroot.hOcc 143
  · exact hroot.hOcc 150
  · exact hroot.hOcc 156
  · exact hroot.hOcc 162
  · exact hroot.hOcc 172
  · exact hroot.hOcc 174
  · exact hroot.hOcc 175
  · exact hroot.hOcc 207
  · exact hroot.hOcc 212
  · exact hroot.hOcc 213
  · exact hroot.hOcc 214
  · exact hroot.hOcc 217
  · exact hroot.hOcc 226
  · exact hroot.hOcc 233
  · exact hroot.hOcc 234
  · exact hroot.hOcc 235
  · exact hroot.hOcc 236
  · exact hroot.hOcc 240
  · exact hroot.hOcc 241
  · exact hroot.hOcc 246
  · change (∑ j, (-1 : Int) * x j) ≤ -plane456GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (20 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (26 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (28 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (32 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (38 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (42 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (44 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (48 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (51 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (53 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (55 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (58 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 58
  · change (∑ k, (if k = (60 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 60
  · change (∑ k, (if k = (24 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (31 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (6 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6

end QiushiMatmul
