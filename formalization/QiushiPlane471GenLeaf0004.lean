import QiushiPlane471GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane471GenLeaf0004Refs : Fin 64 → RowRef 304 63 := ![.occ 12, .occ 13, .occ 21, .occ 28, .occ 31, .occ 33, .occ 47, .occ 65, .occ 69, .occ 85, .occ 90, .occ 91, .occ 93, .occ 95, .occ 110, .occ 116, .occ 118, .occ 119, .occ 121, .occ 145, .occ 157, .occ 171, .occ 182, .occ 195, .occ 198, .occ 201, .occ 205, .occ 212, .occ 216, .occ 221, .occ 227, .occ 230, .occ 235, .occ 241, .occ 243, .occ 259, .occ 263, .occ 264, .occ 265, .occ 274, .occ 277, .occ 278, .occ 287, .occ 288, .occ 290, .occ 291, .occ 301, .sumGe, .nonneg 10, .nonneg 13, .nonneg 17, .nonneg 18, .nonneg 26, .nonneg 30, .nonneg 32, .nonneg 34, .nonneg 49, .nonneg 50, .nonneg 52, .nonneg 59, .nonneg 61, .branchLe 48 (0), .branchLe 14 (0), .branchGe 38 (1)]

def plane471GenLeaf0004Mult : Fin 64 → Nat := ![252450, 137608, 6060, 127486, 23676, 18260, 50404, 89998, 14348, 71772, 21704, 21314, 51494, 59838, 48690, 106620, 25196, 53948, 14404, 57502, 41064, 24704, 89136, 16482, 2344, 32124, 77434, 9548, 6546, 32918, 72414, 7420, 12918, 43088, 105456, 45612, 17166, 34012, 61106, 3086, 18086, 57104, 96457, 35041, 8285, 36413, 25832, 332528, 102820, 6004, 5346, 87488, 174846, 69816, 14404, 55752, 93492, 21336, 2362, 162782, 130272, 300476, 332528, 1291732]

theorem plane471GenLeaf0004 (x : Fin 63 → Int)
    (hroot : plane471GenOccSys.RootHolds x)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hUB_48 : x 48 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane471GenLeaf0004Refs i).resolveCoeff plane471GenOccSys j)
    (fun i => (plane471GenLeaf0004Refs i).resolveRhs plane471GenOccSys) plane471GenLeaf0004Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane471GenLeaf0004Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 12
  · exact hroot.hOcc 13
  · exact hroot.hOcc 21
  · exact hroot.hOcc 28
  · exact hroot.hOcc 31
  · exact hroot.hOcc 33
  · exact hroot.hOcc 47
  · exact hroot.hOcc 65
  · exact hroot.hOcc 69
  · exact hroot.hOcc 85
  · exact hroot.hOcc 90
  · exact hroot.hOcc 91
  · exact hroot.hOcc 93
  · exact hroot.hOcc 95
  · exact hroot.hOcc 110
  · exact hroot.hOcc 116
  · exact hroot.hOcc 118
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 145
  · exact hroot.hOcc 157
  · exact hroot.hOcc 171
  · exact hroot.hOcc 182
  · exact hroot.hOcc 195
  · exact hroot.hOcc 198
  · exact hroot.hOcc 201
  · exact hroot.hOcc 205
  · exact hroot.hOcc 212
  · exact hroot.hOcc 216
  · exact hroot.hOcc 221
  · exact hroot.hOcc 227
  · exact hroot.hOcc 230
  · exact hroot.hOcc 235
  · exact hroot.hOcc 241
  · exact hroot.hOcc 243
  · exact hroot.hOcc 259
  · exact hroot.hOcc 263
  · exact hroot.hOcc 264
  · exact hroot.hOcc 265
  · exact hroot.hOcc 274
  · exact hroot.hOcc 277
  · exact hroot.hOcc 278
  · exact hroot.hOcc 287
  · exact hroot.hOcc 288
  · exact hroot.hOcc 290
  · exact hroot.hOcc 291
  · exact hroot.hOcc 301
  · change (∑ j, (-1 : Int) * x j) ≤ -plane471GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (13 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (17 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (18 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (26 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (30 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (32 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (34 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 34
  · change (∑ k, (if k = (49 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (50 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (52 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (59 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (61 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 61
  · change (∑ k, (if k = (48 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_48
  · change (∑ k, (if k = (14 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (38 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38

end QiushiMatmul
