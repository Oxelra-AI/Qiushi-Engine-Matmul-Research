import QiushiPlane463GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane463GenLeaf0005Refs : Fin 64 → RowRef 278 63 := ![.occ 17, .occ 18, .occ 20, .occ 27, .occ 28, .occ 29, .occ 30, .occ 31, .occ 35, .occ 39, .occ 41, .occ 52, .occ 53, .occ 72, .occ 79, .occ 101, .occ 108, .occ 113, .occ 123, .occ 127, .occ 128, .occ 133, .occ 152, .occ 154, .occ 155, .occ 173, .occ 175, .occ 177, .occ 186, .occ 188, .occ 202, .occ 203, .occ 211, .occ 212, .occ 216, .occ 217, .occ 219, .occ 222, .occ 234, .occ 235, .occ 236, .occ 244, .occ 246, .occ 251, .occ 263, .occ 268, .occ 269, .occ 270, .occ 274, .occ 276, .sumGe, .nonneg 0, .nonneg 12, .nonneg 13, .nonneg 15, .nonneg 18, .nonneg 39, .nonneg 41, .nonneg 48, .branchLe 24 (0), .branchLe 60 (0), .branchLe 21 (0), .branchLe 19 (0), .branchGe 47 (1)]

def plane463GenLeaf0005Mult : Fin 64 → Nat := ![3744, 15716, 3708, 144, 20218, 9484, 3718, 24602, 1188, 1296, 576, 612, 180, 3904, 954, 9190, 23146, 21506, 13768, 2802, 792, 54, 5110, 1044, 5502, 216, 576, 5880, 1995, 144, 1275, 13299, 6798, 1986, 3160, 1700, 9341, 4317, 4826, 8005, 450, 342, 6933, 2376, 477, 1170, 1120, 1661, 1287, 12669, 35641, 43276, 5584, 2160, 144, 216, 288, 1260, 46408, 29528, 22972, 1692, 31328, 185536]

theorem plane463GenLeaf0005 (x : Fin 63 → Int)
    (hroot : plane463GenOccSys.RootHolds x)
    (hLB_47 : (1 : Int) ≤ x 47)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_60 : x 60 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane463GenLeaf0005Refs i).resolveCoeff plane463GenOccSys j)
    (fun i => (plane463GenLeaf0005Refs i).resolveRhs plane463GenOccSys) plane463GenLeaf0005Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane463GenLeaf0005Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 17
  · exact hroot.hOcc 18
  · exact hroot.hOcc 20
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 29
  · exact hroot.hOcc 30
  · exact hroot.hOcc 31
  · exact hroot.hOcc 35
  · exact hroot.hOcc 39
  · exact hroot.hOcc 41
  · exact hroot.hOcc 52
  · exact hroot.hOcc 53
  · exact hroot.hOcc 72
  · exact hroot.hOcc 79
  · exact hroot.hOcc 101
  · exact hroot.hOcc 108
  · exact hroot.hOcc 113
  · exact hroot.hOcc 123
  · exact hroot.hOcc 127
  · exact hroot.hOcc 128
  · exact hroot.hOcc 133
  · exact hroot.hOcc 152
  · exact hroot.hOcc 154
  · exact hroot.hOcc 155
  · exact hroot.hOcc 173
  · exact hroot.hOcc 175
  · exact hroot.hOcc 177
  · exact hroot.hOcc 186
  · exact hroot.hOcc 188
  · exact hroot.hOcc 202
  · exact hroot.hOcc 203
  · exact hroot.hOcc 211
  · exact hroot.hOcc 212
  · exact hroot.hOcc 216
  · exact hroot.hOcc 217
  · exact hroot.hOcc 219
  · exact hroot.hOcc 222
  · exact hroot.hOcc 234
  · exact hroot.hOcc 235
  · exact hroot.hOcc 236
  · exact hroot.hOcc 244
  · exact hroot.hOcc 246
  · exact hroot.hOcc 251
  · exact hroot.hOcc 263
  · exact hroot.hOcc 268
  · exact hroot.hOcc 269
  · exact hroot.hOcc 270
  · exact hroot.hOcc 274
  · exact hroot.hOcc 276
  · change (∑ j, (-1 : Int) * x j) ≤ -plane463GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (12 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (13 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (15 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (18 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (39 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (41 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (48 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (24 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (60 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_60
  · change (∑ k, (if k = (21 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (19 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (47 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_47

end QiushiMatmul
