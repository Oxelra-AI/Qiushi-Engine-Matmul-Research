import QiushiPlane463GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane463GenLeaf0008Refs : Fin 64 → RowRef 278 63 := ![.occ 3, .occ 7, .occ 8, .occ 9, .occ 18, .occ 28, .occ 32, .occ 38, .occ 65, .occ 69, .occ 76, .occ 79, .occ 83, .occ 84, .occ 88, .occ 103, .occ 114, .occ 118, .occ 127, .occ 146, .occ 153, .occ 161, .occ 173, .occ 174, .occ 187, .occ 189, .occ 190, .occ 204, .occ 205, .occ 214, .occ 215, .occ 218, .occ 222, .occ 231, .occ 243, .occ 244, .occ 253, .occ 254, .occ 258, .occ 264, .occ 268, .occ 270, .occ 272, .occ 273, .occ 274, .sumGe, .nonneg 0, .nonneg 10, .nonneg 11, .nonneg 12, .nonneg 37, .nonneg 39, .nonneg 43, .nonneg 44, .nonneg 48, .nonneg 49, .nonneg 56, .nonneg 57, .nonneg 61, .branchLe 15 (0), .branchLe 24 (0), .branchLe 60 (0), .branchGe 21 (1), .branchGe 35 (1)]

def plane463GenLeaf0008Mult : Fin 64 → Nat := ![309799, 270559, 180930, 17802, 97582, 296564, 48201, 7072, 116131, 251510, 26696, 70370, 184822, 193183, 178310, 274175, 31108, 342, 65134, 133626, 153564, 110484, 16301, 34498, 66670, 111283, 18507, 2824, 93413, 192546, 54447, 8524, 56481, 152551, 63220, 13271, 18427, 33726, 72213, 8136, 9498, 138330, 99774, 4262, 160798, 546177, 270938, 144964, 16154, 403440, 48568, 64203, 4022, 4482, 41838, 410150, 136774, 116642, 191965, 232828, 81184, 122680, 3020823, 643250]

theorem plane463GenLeaf0008 (x : Fin 63 → Int)
    (hroot : plane463GenOccSys.RootHolds x)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_60 : x 60 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane463GenLeaf0008Refs i).resolveCoeff plane463GenOccSys j)
    (fun i => (plane463GenLeaf0008Refs i).resolveRhs plane463GenOccSys) plane463GenLeaf0008Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane463GenLeaf0008Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 3
  · exact hroot.hOcc 7
  · exact hroot.hOcc 8
  · exact hroot.hOcc 9
  · exact hroot.hOcc 18
  · exact hroot.hOcc 28
  · exact hroot.hOcc 32
  · exact hroot.hOcc 38
  · exact hroot.hOcc 65
  · exact hroot.hOcc 69
  · exact hroot.hOcc 76
  · exact hroot.hOcc 79
  · exact hroot.hOcc 83
  · exact hroot.hOcc 84
  · exact hroot.hOcc 88
  · exact hroot.hOcc 103
  · exact hroot.hOcc 114
  · exact hroot.hOcc 118
  · exact hroot.hOcc 127
  · exact hroot.hOcc 146
  · exact hroot.hOcc 153
  · exact hroot.hOcc 161
  · exact hroot.hOcc 173
  · exact hroot.hOcc 174
  · exact hroot.hOcc 187
  · exact hroot.hOcc 189
  · exact hroot.hOcc 190
  · exact hroot.hOcc 204
  · exact hroot.hOcc 205
  · exact hroot.hOcc 214
  · exact hroot.hOcc 215
  · exact hroot.hOcc 218
  · exact hroot.hOcc 222
  · exact hroot.hOcc 231
  · exact hroot.hOcc 243
  · exact hroot.hOcc 244
  · exact hroot.hOcc 253
  · exact hroot.hOcc 254
  · exact hroot.hOcc 258
  · exact hroot.hOcc 264
  · exact hroot.hOcc 268
  · exact hroot.hOcc 270
  · exact hroot.hOcc 272
  · exact hroot.hOcc 273
  · exact hroot.hOcc 274
  · change (∑ j, (-1 : Int) * x j) ≤ -plane463GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (10 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (11 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (12 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (37 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (39 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (43 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 43
  · change (∑ k, (if k = (44 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (48 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (49 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (56 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 56
  · change (∑ k, (if k = (57 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 57
  · change (∑ k, (if k = (61 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 61
  · change (∑ k, (if k = (15 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (24 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (60 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_60
  · change (∑ k, (if k = (21 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21
  · change (∑ k, (if k = (35 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35

end QiushiMatmul
