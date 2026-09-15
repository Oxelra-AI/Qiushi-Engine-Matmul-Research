import QiushiPlane426GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane426GenLeaf0013Refs : Fin 59 → RowRef 340 58 := ![.occ 6, .occ 8, .occ 13, .occ 63, .occ 67, .occ 68, .occ 70, .occ 71, .occ 77, .occ 86, .occ 88, .occ 89, .occ 98, .occ 99, .occ 104, .occ 105, .occ 113, .occ 116, .occ 122, .occ 126, .occ 132, .occ 140, .occ 144, .occ 164, .occ 214, .occ 228, .occ 230, .occ 238, .occ 242, .occ 249, .occ 307, .occ 310, .occ 312, .occ 313, .occ 316, .occ 318, .occ 323, .occ 333, .occ 334, .sumGe, .nonneg 13, .nonneg 16, .nonneg 19, .nonneg 24, .nonneg 25, .nonneg 26, .nonneg 33, .nonneg 36, .nonneg 40, .nonneg 47, .nonneg 50, .branchLe 43 (0), .branchLe 14 (0), .branchGe 1 (1), .branchLe 35 (0), .branchGe 4 (1), .branchLe 29 (0), .branchGe 20 (1), .branchGe 11 (1)]

def plane426GenLeaf0013Mult : Fin 59 → Nat := ![2499, 2300, 1050, 5545, 1649, 2946, 4803, 3044, 2936, 823, 1750, 429, 1034, 555, 598, 2777, 4973, 3045, 2854, 1223, 189, 534, 2381, 3797, 1199, 453, 4016, 523, 1038, 115, 3753, 19, 2105, 1080, 996, 2573, 17, 2001, 428, 8563, 2237, 1868, 4704, 3067, 5375, 904, 1035, 1814, 562, 1210, 1928, 6982, 2594, 10148, 3989, 11777, 5305, 16680, 23264]

theorem plane426GenLeaf0013 (x : Fin 58 → Int)
    (hroot : plane426GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hUB_43 : x 43 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane426GenLeaf0013Refs i).resolveCoeff plane426GenOccSys j)
    (fun i => (plane426GenLeaf0013Refs i).resolveRhs plane426GenOccSys) plane426GenLeaf0013Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane426GenLeaf0013Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 6
  · exact hroot.hOcc 8
  · exact hroot.hOcc 13
  · exact hroot.hOcc 63
  · exact hroot.hOcc 67
  · exact hroot.hOcc 68
  · exact hroot.hOcc 70
  · exact hroot.hOcc 71
  · exact hroot.hOcc 77
  · exact hroot.hOcc 86
  · exact hroot.hOcc 88
  · exact hroot.hOcc 89
  · exact hroot.hOcc 98
  · exact hroot.hOcc 99
  · exact hroot.hOcc 104
  · exact hroot.hOcc 105
  · exact hroot.hOcc 113
  · exact hroot.hOcc 116
  · exact hroot.hOcc 122
  · exact hroot.hOcc 126
  · exact hroot.hOcc 132
  · exact hroot.hOcc 140
  · exact hroot.hOcc 144
  · exact hroot.hOcc 164
  · exact hroot.hOcc 214
  · exact hroot.hOcc 228
  · exact hroot.hOcc 230
  · exact hroot.hOcc 238
  · exact hroot.hOcc 242
  · exact hroot.hOcc 249
  · exact hroot.hOcc 307
  · exact hroot.hOcc 310
  · exact hroot.hOcc 312
  · exact hroot.hOcc 313
  · exact hroot.hOcc 316
  · exact hroot.hOcc 318
  · exact hroot.hOcc 323
  · exact hroot.hOcc 333
  · exact hroot.hOcc 334
  · change (∑ j, (-1 : Int) * x j) ≤ -plane426GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (13 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (16 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (19 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (24 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (25 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (26 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (33 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (36 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (40 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (47 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (50 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (43 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (14 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (35 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (4 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (29 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (20 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20
  · change (∑ k, (if k = (11 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11

end QiushiMatmul
