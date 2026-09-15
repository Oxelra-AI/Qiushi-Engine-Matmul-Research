import QiushiPlane463GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane463GenLeaf0003Refs : Fin 64 → RowRef 278 63 := ![.occ 2, .occ 6, .occ 8, .occ 12, .occ 13, .occ 14, .occ 19, .occ 20, .occ 24, .occ 27, .occ 37, .occ 43, .occ 47, .occ 49, .occ 52, .occ 58, .occ 76, .occ 79, .occ 95, .occ 96, .occ 108, .occ 112, .occ 114, .occ 115, .occ 126, .occ 130, .occ 154, .occ 158, .occ 168, .occ 172, .occ 182, .occ 183, .occ 186, .occ 213, .occ 218, .occ 222, .occ 248, .occ 263, .occ 264, .occ 266, .occ 268, .occ 274, .occ 275, .occ 276, .sumGe, .nonneg 0, .nonneg 10, .nonneg 12, .nonneg 13, .nonneg 37, .nonneg 40, .nonneg 41, .nonneg 48, .nonneg 49, .nonneg 56, .nonneg 59, .branchLe 15 (0), .branchLe 24 (0), .branchLe 60 (0), .branchLe 21 (0), .branchLe 19 (0), .branchLe 47 (0), .branchLe 22 (0), .branchGe 20 (1)]

def plane463GenLeaf0003Mult : Fin 64 → Nat := ![13561, 57616, 2968, 9396, 9147, 1853, 9288, 7074, 2026, 5307, 23882, 21002, 10394, 13767, 5288, 37107, 38676, 34645, 572, 14338, 8281, 12842, 8292, 38060, 6847, 4392, 20140, 20129, 14118, 20299, 6425, 3618, 9826, 2716, 344, 30916, 2716, 1096, 3450, 8265, 27493, 6400, 2040, 5759, 75731, 26063, 62003, 23267, 46463, 16494, 29028, 5820, 3118, 25473, 9455, 17564, 60436, 36037, 61707, 65881, 47858, 61691, 41728, 226382]

theorem plane463GenLeaf0003 (x : Fin 63 → Int)
    (hroot : plane463GenOccSys.RootHolds x)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_60 : x 60 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_47 : x 47 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane463GenLeaf0003Refs i).resolveCoeff plane463GenOccSys j)
    (fun i => (plane463GenLeaf0003Refs i).resolveRhs plane463GenOccSys) plane463GenLeaf0003Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane463GenLeaf0003Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · exact hroot.hOcc 6
  · exact hroot.hOcc 8
  · exact hroot.hOcc 12
  · exact hroot.hOcc 13
  · exact hroot.hOcc 14
  · exact hroot.hOcc 19
  · exact hroot.hOcc 20
  · exact hroot.hOcc 24
  · exact hroot.hOcc 27
  · exact hroot.hOcc 37
  · exact hroot.hOcc 43
  · exact hroot.hOcc 47
  · exact hroot.hOcc 49
  · exact hroot.hOcc 52
  · exact hroot.hOcc 58
  · exact hroot.hOcc 76
  · exact hroot.hOcc 79
  · exact hroot.hOcc 95
  · exact hroot.hOcc 96
  · exact hroot.hOcc 108
  · exact hroot.hOcc 112
  · exact hroot.hOcc 114
  · exact hroot.hOcc 115
  · exact hroot.hOcc 126
  · exact hroot.hOcc 130
  · exact hroot.hOcc 154
  · exact hroot.hOcc 158
  · exact hroot.hOcc 168
  · exact hroot.hOcc 172
  · exact hroot.hOcc 182
  · exact hroot.hOcc 183
  · exact hroot.hOcc 186
  · exact hroot.hOcc 213
  · exact hroot.hOcc 218
  · exact hroot.hOcc 222
  · exact hroot.hOcc 248
  · exact hroot.hOcc 263
  · exact hroot.hOcc 264
  · exact hroot.hOcc 266
  · exact hroot.hOcc 268
  · exact hroot.hOcc 274
  · exact hroot.hOcc 275
  · exact hroot.hOcc 276
  · change (∑ j, (-1 : Int) * x j) ≤ -plane463GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (10 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (12 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (13 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (37 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (40 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (41 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (48 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (49 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (56 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 56
  · change (∑ k, (if k = (59 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (15 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (24 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (60 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_60
  · change (∑ k, (if k = (21 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (19 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (47 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_47
  · change (∑ k, (if k = (22 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (20 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20

end QiushiMatmul
