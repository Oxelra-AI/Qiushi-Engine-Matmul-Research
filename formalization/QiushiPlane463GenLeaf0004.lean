import QiushiPlane463GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane463GenLeaf0004Refs : Fin 64 → RowRef 278 63 := ![.occ 1, .occ 5, .occ 13, .occ 14, .occ 29, .occ 44, .occ 49, .occ 53, .occ 60, .occ 63, .occ 75, .occ 79, .occ 96, .occ 97, .occ 102, .occ 109, .occ 110, .occ 114, .occ 148, .occ 150, .occ 156, .occ 162, .occ 170, .occ 184, .occ 185, .occ 187, .occ 188, .occ 201, .occ 208, .occ 213, .occ 214, .occ 218, .occ 222, .occ 223, .occ 236, .occ 244, .occ 257, .occ 263, .occ 268, .occ 269, .occ 270, .occ 271, .occ 272, .occ 273, .occ 274, .occ 276, .sumGe, .nonneg 10, .nonneg 12, .nonneg 39, .nonneg 40, .nonneg 42, .nonneg 48, .nonneg 49, .nonneg 56, .nonneg 57, .nonneg 59, .branchLe 15 (0), .branchLe 24 (0), .branchLe 60 (0), .branchLe 21 (0), .branchLe 19 (0), .branchLe 47 (0), .branchGe 22 (1)]

def plane463GenLeaf0004Mult : Fin 64 → Nat := ![168216, 228466, 4964, 2878, 18482, 9688, 15538, 158986, 50152, 98848, 156250, 101442, 7292, 60118, 28638, 86288, 18310, 62234, 69044, 69250, 78832, 11446, 84491, 10300, 20458, 24842, 12282, 19451, 1599, 15190, 49685, 109663, 44872, 33042, 8056, 83702, 45725, 12223, 38449, 98477, 5757, 58544, 1419, 11087, 52232, 35863, 384859, 248056, 148314, 11880, 6780, 160950, 80338, 186390, 22816, 11972, 96032, 127520, 144762, 210266, 275766, 299816, 226280, 1023826]

theorem plane463GenLeaf0004 (x : Fin 63 → Int)
    (hroot : plane463GenOccSys.RootHolds x)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_60 : x 60 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_47 : x 47 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane463GenLeaf0004Refs i).resolveCoeff plane463GenOccSys j)
    (fun i => (plane463GenLeaf0004Refs i).resolveRhs plane463GenOccSys) plane463GenLeaf0004Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane463GenLeaf0004Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · exact hroot.hOcc 5
  · exact hroot.hOcc 13
  · exact hroot.hOcc 14
  · exact hroot.hOcc 29
  · exact hroot.hOcc 44
  · exact hroot.hOcc 49
  · exact hroot.hOcc 53
  · exact hroot.hOcc 60
  · exact hroot.hOcc 63
  · exact hroot.hOcc 75
  · exact hroot.hOcc 79
  · exact hroot.hOcc 96
  · exact hroot.hOcc 97
  · exact hroot.hOcc 102
  · exact hroot.hOcc 109
  · exact hroot.hOcc 110
  · exact hroot.hOcc 114
  · exact hroot.hOcc 148
  · exact hroot.hOcc 150
  · exact hroot.hOcc 156
  · exact hroot.hOcc 162
  · exact hroot.hOcc 170
  · exact hroot.hOcc 184
  · exact hroot.hOcc 185
  · exact hroot.hOcc 187
  · exact hroot.hOcc 188
  · exact hroot.hOcc 201
  · exact hroot.hOcc 208
  · exact hroot.hOcc 213
  · exact hroot.hOcc 214
  · exact hroot.hOcc 218
  · exact hroot.hOcc 222
  · exact hroot.hOcc 223
  · exact hroot.hOcc 236
  · exact hroot.hOcc 244
  · exact hroot.hOcc 257
  · exact hroot.hOcc 263
  · exact hroot.hOcc 268
  · exact hroot.hOcc 269
  · exact hroot.hOcc 270
  · exact hroot.hOcc 271
  · exact hroot.hOcc 272
  · exact hroot.hOcc 273
  · exact hroot.hOcc 274
  · exact hroot.hOcc 276
  · change (∑ j, (-1 : Int) * x j) ≤ -plane463GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (12 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (39 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (40 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (42 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (48 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (49 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (56 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 56
  · change (∑ k, (if k = (57 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 57
  · change (∑ k, (if k = (59 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (15 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (24 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (60 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_60
  · change (∑ k, (if k = (21 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (19 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (47 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_47
  · change (∑ k, (if k = (22 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22

end QiushiMatmul
