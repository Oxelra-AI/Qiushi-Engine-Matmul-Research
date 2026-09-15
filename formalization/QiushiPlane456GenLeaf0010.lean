import QiushiPlane456GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane456GenLeaf0010Refs : Fin 61 → RowRef 248 63 := ![.occ 2, .occ 4, .occ 5, .occ 20, .occ 23, .occ 26, .occ 28, .occ 41, .occ 51, .occ 56, .occ 72, .occ 78, .occ 81, .occ 83, .occ 102, .occ 106, .occ 122, .occ 128, .occ 129, .occ 133, .occ 134, .occ 137, .occ 139, .occ 141, .occ 145, .occ 157, .occ 158, .occ 160, .occ 165, .occ 166, .occ 167, .occ 184, .occ 193, .occ 199, .occ 202, .occ 204, .occ 205, .occ 210, .occ 211, .occ 222, .occ 224, .occ 240, .occ 242, .occ 243, .occ 244, .sumGe, .nonneg 0, .nonneg 2, .nonneg 21, .nonneg 29, .nonneg 32, .nonneg 34, .nonneg 37, .nonneg 42, .nonneg 49, .nonneg 50, .nonneg 58, .nonneg 59, .nonneg 60, .nonneg 62, .branchGe 24 (1)]

def plane456GenLeaf0010Mult : Fin 61 → Nat := ![3640, 952, 880, 5692, 12072, 1832, 904, 8696, 11956, 23396, 6412, 7944, 15606, 1350, 380, 928, 4592, 320, 2296, 24, 26004, 3126, 17652, 24, 1422, 446, 494, 1603, 217, 2440, 5289, 1130, 467, 3540, 7135, 1149, 695, 1363, 687, 13673, 253, 9952, 309, 2379, 6199, 26004, 952, 904, 2784, 2760, 24, 904, 67696, 4348, 5228, 1808, 24, 24, 4616, 61272, 162180]

theorem plane456GenLeaf0010 (x : Fin 63 → Int)
    (hroot : plane456GenOccSys.RootHolds x)
    (hLB_24 : (1 : Int) ≤ x 24)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane456GenLeaf0010Refs i).resolveCoeff plane456GenOccSys j)
    (fun i => (plane456GenLeaf0010Refs i).resolveRhs plane456GenOccSys) plane456GenLeaf0010Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane456GenLeaf0010Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · exact hroot.hOcc 4
  · exact hroot.hOcc 5
  · exact hroot.hOcc 20
  · exact hroot.hOcc 23
  · exact hroot.hOcc 26
  · exact hroot.hOcc 28
  · exact hroot.hOcc 41
  · exact hroot.hOcc 51
  · exact hroot.hOcc 56
  · exact hroot.hOcc 72
  · exact hroot.hOcc 78
  · exact hroot.hOcc 81
  · exact hroot.hOcc 83
  · exact hroot.hOcc 102
  · exact hroot.hOcc 106
  · exact hroot.hOcc 122
  · exact hroot.hOcc 128
  · exact hroot.hOcc 129
  · exact hroot.hOcc 133
  · exact hroot.hOcc 134
  · exact hroot.hOcc 137
  · exact hroot.hOcc 139
  · exact hroot.hOcc 141
  · exact hroot.hOcc 145
  · exact hroot.hOcc 157
  · exact hroot.hOcc 158
  · exact hroot.hOcc 160
  · exact hroot.hOcc 165
  · exact hroot.hOcc 166
  · exact hroot.hOcc 167
  · exact hroot.hOcc 184
  · exact hroot.hOcc 193
  · exact hroot.hOcc 199
  · exact hroot.hOcc 202
  · exact hroot.hOcc 204
  · exact hroot.hOcc 205
  · exact hroot.hOcc 210
  · exact hroot.hOcc 211
  · exact hroot.hOcc 222
  · exact hroot.hOcc 224
  · exact hroot.hOcc 240
  · exact hroot.hOcc 242
  · exact hroot.hOcc 243
  · exact hroot.hOcc 244
  · change (∑ j, (-1 : Int) * x j) ≤ -plane456GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (2 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (21 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (29 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (32 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (34 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 34
  · change (∑ k, (if k = (37 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (42 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (49 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (50 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (58 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 58
  · change (∑ k, (if k = (59 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (60 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 60
  · change (∑ k, (if k = (62 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 62
  · change (∑ k, (if k = (24 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24

end QiushiMatmul
