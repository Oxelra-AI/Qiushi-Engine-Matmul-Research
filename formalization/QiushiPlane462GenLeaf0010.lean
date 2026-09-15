import QiushiPlane462GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane462GenLeaf0010Refs : Fin 63 → RowRef 294 62 := ![.occ 2, .occ 3, .occ 14, .occ 25, .occ 62, .occ 67, .occ 72, .occ 73, .occ 78, .occ 80, .occ 86, .occ 91, .occ 92, .occ 96, .occ 99, .occ 100, .occ 102, .occ 110, .occ 111, .occ 118, .occ 124, .occ 153, .occ 156, .occ 157, .occ 158, .occ 164, .occ 168, .occ 171, .occ 175, .occ 184, .occ 188, .occ 193, .occ 198, .occ 199, .occ 200, .occ 203, .occ 207, .occ 214, .occ 244, .occ 247, .occ 256, .occ 257, .occ 260, .occ 269, .occ 276, .occ 283, .occ 293, .sumGe, .nonneg 0, .nonneg 7, .nonneg 8, .nonneg 10, .nonneg 11, .nonneg 12, .nonneg 13, .nonneg 19, .nonneg 42, .nonneg 50, .nonneg 52, .branchGe 3 (1), .branchLe 5 (0), .branchGe 2 (1), .branchGe 45 (1)]

def plane462GenLeaf0010Mult : Fin 63 → Nat := ![2936, 1344, 1120, 208, 1224, 1280, 752, 556, 996, 708, 508, 930, 650, 716, 874, 482, 208, 940, 1016, 638, 832, 296, 604, 158, 1312, 268, 1444, 416, 964, 232, 880, 808, 1024, 84, 808, 232, 376, 160, 554, 1272, 36, 488, 1090, 317, 1107, 97, 219, 5448, 3648, 5132, 848, 212, 700, 1660, 868, 640, 1192, 112, 752, 4824, 5448, 6980, 11032]

theorem plane462GenLeaf0010 (x : Fin 62 → Int)
    (hroot : plane462GenOccSys.RootHolds x)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_45 : (1 : Int) ≤ x 45)
    (hUB_5 : x 5 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane462GenLeaf0010Refs i).resolveCoeff plane462GenOccSys j)
    (fun i => (plane462GenLeaf0010Refs i).resolveRhs plane462GenOccSys) plane462GenLeaf0010Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane462GenLeaf0010Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · exact hroot.hOcc 3
  · exact hroot.hOcc 14
  · exact hroot.hOcc 25
  · exact hroot.hOcc 62
  · exact hroot.hOcc 67
  · exact hroot.hOcc 72
  · exact hroot.hOcc 73
  · exact hroot.hOcc 78
  · exact hroot.hOcc 80
  · exact hroot.hOcc 86
  · exact hroot.hOcc 91
  · exact hroot.hOcc 92
  · exact hroot.hOcc 96
  · exact hroot.hOcc 99
  · exact hroot.hOcc 100
  · exact hroot.hOcc 102
  · exact hroot.hOcc 110
  · exact hroot.hOcc 111
  · exact hroot.hOcc 118
  · exact hroot.hOcc 124
  · exact hroot.hOcc 153
  · exact hroot.hOcc 156
  · exact hroot.hOcc 157
  · exact hroot.hOcc 158
  · exact hroot.hOcc 164
  · exact hroot.hOcc 168
  · exact hroot.hOcc 171
  · exact hroot.hOcc 175
  · exact hroot.hOcc 184
  · exact hroot.hOcc 188
  · exact hroot.hOcc 193
  · exact hroot.hOcc 198
  · exact hroot.hOcc 199
  · exact hroot.hOcc 200
  · exact hroot.hOcc 203
  · exact hroot.hOcc 207
  · exact hroot.hOcc 214
  · exact hroot.hOcc 244
  · exact hroot.hOcc 247
  · exact hroot.hOcc 256
  · exact hroot.hOcc 257
  · exact hroot.hOcc 260
  · exact hroot.hOcc 269
  · exact hroot.hOcc 276
  · exact hroot.hOcc 283
  · exact hroot.hOcc 293
  · change (∑ j, (-1 : Int) * x j) ≤ -plane462GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (7 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (8 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (10 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (11 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (12 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (13 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (19 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (42 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (50 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (52 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (3 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3
  · change (∑ k, (if k = (5 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (2 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (45 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_45

end QiushiMatmul
