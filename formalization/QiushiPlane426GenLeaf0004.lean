import QiushiPlane426GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane426GenLeaf0004Refs : Fin 59 → RowRef 340 58 := ![.occ 5, .occ 16, .occ 32, .occ 54, .occ 71, .occ 76, .occ 116, .occ 121, .occ 124, .occ 126, .occ 135, .occ 138, .occ 142, .occ 144, .occ 147, .occ 166, .occ 184, .occ 194, .occ 200, .occ 237, .occ 238, .occ 255, .occ 266, .occ 278, .occ 280, .occ 281, .occ 282, .occ 290, .occ 304, .occ 311, .occ 321, .occ 322, .occ 328, .occ 329, .occ 331, .occ 334, .occ 335, .sumGe, .nonneg 5, .nonneg 16, .nonneg 17, .nonneg 19, .nonneg 22, .nonneg 24, .nonneg 25, .nonneg 26, .nonneg 28, .nonneg 32, .nonneg 33, .nonneg 36, .nonneg 39, .nonneg 40, .nonneg 46, .nonneg 52, .branchLe 43 (0), .branchLe 14 (0), .branchLe 1 (0), .branchGe 13 (1), .branchLe 21 (0)]

def plane426GenLeaf0004Mult : Fin 59 → Nat := ![22396, 28988, 9248, 10428, 13732, 21132, 3216, 25624, 16492, 22460, 4920, 6168, 31252, 15416, 6808, 240, 3976, 8372, 19204, 5148, 9064, 7864, 4424, 11119, 4413, 9201, 8479, 2976, 6364, 11832, 23407, 15613, 2376, 31309, 30251, 20387, 38569, 123532, 58108, 124756, 103980, 83860, 3776, 15692, 812, 22000, 13852, 12336, 4544, 29272, 11968, 14088, 560, 40640, 62648, 123532, 97968, 111540, 118180]

theorem plane426GenLeaf0004 (x : Fin 58 → Int)
    (hroot : plane426GenOccSys.RootHolds x)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hUB_43 : x 43 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane426GenLeaf0004Refs i).resolveCoeff plane426GenOccSys j)
    (fun i => (plane426GenLeaf0004Refs i).resolveRhs plane426GenOccSys) plane426GenLeaf0004Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane426GenLeaf0004Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · exact hroot.hOcc 16
  · exact hroot.hOcc 32
  · exact hroot.hOcc 54
  · exact hroot.hOcc 71
  · exact hroot.hOcc 76
  · exact hroot.hOcc 116
  · exact hroot.hOcc 121
  · exact hroot.hOcc 124
  · exact hroot.hOcc 126
  · exact hroot.hOcc 135
  · exact hroot.hOcc 138
  · exact hroot.hOcc 142
  · exact hroot.hOcc 144
  · exact hroot.hOcc 147
  · exact hroot.hOcc 166
  · exact hroot.hOcc 184
  · exact hroot.hOcc 194
  · exact hroot.hOcc 200
  · exact hroot.hOcc 237
  · exact hroot.hOcc 238
  · exact hroot.hOcc 255
  · exact hroot.hOcc 266
  · exact hroot.hOcc 278
  · exact hroot.hOcc 280
  · exact hroot.hOcc 281
  · exact hroot.hOcc 282
  · exact hroot.hOcc 290
  · exact hroot.hOcc 304
  · exact hroot.hOcc 311
  · exact hroot.hOcc 321
  · exact hroot.hOcc 322
  · exact hroot.hOcc 328
  · exact hroot.hOcc 329
  · exact hroot.hOcc 331
  · exact hroot.hOcc 334
  · exact hroot.hOcc 335
  · change (∑ j, (-1 : Int) * x j) ≤ -plane426GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (16 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (19 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (22 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (24 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (25 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (26 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (28 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (32 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (33 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (36 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (39 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (40 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (46 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (52 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (43 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (14 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (13 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13
  · change (∑ k, (if k = (21 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21

end QiushiMatmul
