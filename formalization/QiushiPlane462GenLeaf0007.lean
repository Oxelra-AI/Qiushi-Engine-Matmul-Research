import QiushiPlane462GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane462GenLeaf0007Refs : Fin 63 → RowRef 294 62 := ![.occ 16, .occ 17, .occ 27, .occ 39, .occ 41, .occ 47, .occ 51, .occ 62, .occ 67, .occ 69, .occ 72, .occ 73, .occ 74, .occ 78, .occ 80, .occ 85, .occ 88, .occ 92, .occ 94, .occ 96, .occ 102, .occ 105, .occ 110, .occ 122, .occ 123, .occ 130, .occ 137, .occ 155, .occ 156, .occ 164, .occ 175, .occ 178, .occ 200, .occ 206, .occ 210, .occ 228, .occ 230, .occ 237, .occ 239, .occ 265, .occ 270, .occ 271, .occ 275, .occ 284, .occ 285, .occ 290, .sumGe, .nonneg 0, .nonneg 7, .nonneg 8, .nonneg 12, .nonneg 40, .nonneg 44, .nonneg 47, .nonneg 49, .nonneg 51, .nonneg 57, .nonneg 61, .branchGe 3 (1), .branchLe 5 (0), .branchLe 2 (0), .branchLe 43 (0), .branchGe 4 (1)]

def plane462GenLeaf0007Mult : Fin 63 → Nat := ![7934980, 813500, 1687398, 1297844, 4203352, 1954078, 2867754, 7764704, 6169061, 1091936, 7222411, 2704028, 756528, 1334418, 2117804, 3069506, 2393460, 3808994, 319664, 7201849, 2620034, 1162264, 4798435, 1595764, 2123734, 1868982, 245317, 559128, 147830, 6931497, 5596930, 30804, 1320862, 658667, 1201268, 785409, 448458, 2859190, 336951, 2200414, 60203, 405403, 3633704, 4208090, 142054, 3197995, 18260556, 22418108, 2802680, 8853264, 468964, 1362044, 865508, 2422124, 208248, 2337772, 5122272, 775688, 27940980, 18260556, 18260556, 13336296, 49737084]

theorem plane462GenLeaf0007 (x : Fin 62 → Int)
    (hroot : plane462GenOccSys.RootHolds x)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_43 : x 43 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane462GenLeaf0007Refs i).resolveCoeff plane462GenOccSys j)
    (fun i => (plane462GenLeaf0007Refs i).resolveRhs plane462GenOccSys) plane462GenLeaf0007Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane462GenLeaf0007Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 16
  · exact hroot.hOcc 17
  · exact hroot.hOcc 27
  · exact hroot.hOcc 39
  · exact hroot.hOcc 41
  · exact hroot.hOcc 47
  · exact hroot.hOcc 51
  · exact hroot.hOcc 62
  · exact hroot.hOcc 67
  · exact hroot.hOcc 69
  · exact hroot.hOcc 72
  · exact hroot.hOcc 73
  · exact hroot.hOcc 74
  · exact hroot.hOcc 78
  · exact hroot.hOcc 80
  · exact hroot.hOcc 85
  · exact hroot.hOcc 88
  · exact hroot.hOcc 92
  · exact hroot.hOcc 94
  · exact hroot.hOcc 96
  · exact hroot.hOcc 102
  · exact hroot.hOcc 105
  · exact hroot.hOcc 110
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 130
  · exact hroot.hOcc 137
  · exact hroot.hOcc 155
  · exact hroot.hOcc 156
  · exact hroot.hOcc 164
  · exact hroot.hOcc 175
  · exact hroot.hOcc 178
  · exact hroot.hOcc 200
  · exact hroot.hOcc 206
  · exact hroot.hOcc 210
  · exact hroot.hOcc 228
  · exact hroot.hOcc 230
  · exact hroot.hOcc 237
  · exact hroot.hOcc 239
  · exact hroot.hOcc 265
  · exact hroot.hOcc 270
  · exact hroot.hOcc 271
  · exact hroot.hOcc 275
  · exact hroot.hOcc 284
  · exact hroot.hOcc 285
  · exact hroot.hOcc 290
  · change (∑ j, (-1 : Int) * x j) ≤ -plane462GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (7 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (8 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (12 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (40 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (44 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (47 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (49 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (51 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (57 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 57
  · change (∑ k, (if k = (61 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 61
  · change (∑ k, (if k = (3 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3
  · change (∑ k, (if k = (5 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (2 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (43 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (4 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
