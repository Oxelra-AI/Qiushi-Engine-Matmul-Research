import QiushiPlane425GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane425GenLeaf0000Refs : Fin 59 → RowRef 202 58 := ![.occ 8, .occ 12, .occ 17, .occ 28, .occ 40, .occ 56, .occ 57, .occ 61, .occ 63, .occ 64, .occ 66, .occ 67, .occ 71, .occ 78, .occ 88, .occ 92, .occ 93, .occ 94, .occ 99, .occ 116, .occ 119, .occ 121, .occ 123, .occ 129, .occ 131, .occ 133, .occ 137, .occ 156, .occ 157, .occ 160, .occ 163, .occ 177, .occ 178, .occ 185, .occ 189, .occ 191, .occ 192, .occ 193, .occ 194, .occ 198, .occ 199, .sumGe, .nonneg 2, .nonneg 3, .nonneg 13, .nonneg 14, .nonneg 15, .nonneg 21, .nonneg 22, .nonneg 24, .nonneg 38, .nonneg 41, .nonneg 48, .nonneg 49, .nonneg 55, .nonneg 56, .branchLe 17 (0), .branchLe 8 (0), .branchLe 47 (0)]

def plane425GenLeaf0000Mult : Fin 59 → Nat := ![13896, 10436, 3804, 25872, 2252, 672, 8352, 2472, 11348, 4652, 22044, 1732, 8876, 388, 28992, 5076, 5816, 18228, 8172, 8664, 3416, 6734, 1190, 6244, 16744, 12896, 11704, 806, 6492, 5210, 8636, 2924, 5010, 4196, 37340, 34179, 44191, 13362, 35368, 29243, 31955, 139568, 36940, 160716, 171668, 57380, 119124, 7168, 10916, 3884, 56892, 31240, 4720, 12272, 62928, 35364, 139568, 48576, 53368]

theorem plane425GenLeaf0000 (x : Fin 58 → Int)
    (hroot : plane425GenOccSys.RootHolds x)
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_47 : x 47 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane425GenLeaf0000Refs i).resolveCoeff plane425GenOccSys j)
    (fun i => (plane425GenLeaf0000Refs i).resolveRhs plane425GenOccSys) plane425GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane425GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 8
  · exact hroot.hOcc 12
  · exact hroot.hOcc 17
  · exact hroot.hOcc 28
  · exact hroot.hOcc 40
  · exact hroot.hOcc 56
  · exact hroot.hOcc 57
  · exact hroot.hOcc 61
  · exact hroot.hOcc 63
  · exact hroot.hOcc 64
  · exact hroot.hOcc 66
  · exact hroot.hOcc 67
  · exact hroot.hOcc 71
  · exact hroot.hOcc 78
  · exact hroot.hOcc 88
  · exact hroot.hOcc 92
  · exact hroot.hOcc 93
  · exact hroot.hOcc 94
  · exact hroot.hOcc 99
  · exact hroot.hOcc 116
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 123
  · exact hroot.hOcc 129
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 137
  · exact hroot.hOcc 156
  · exact hroot.hOcc 157
  · exact hroot.hOcc 160
  · exact hroot.hOcc 163
  · exact hroot.hOcc 177
  · exact hroot.hOcc 178
  · exact hroot.hOcc 185
  · exact hroot.hOcc 189
  · exact hroot.hOcc 191
  · exact hroot.hOcc 192
  · exact hroot.hOcc 193
  · exact hroot.hOcc 194
  · exact hroot.hOcc 198
  · exact hroot.hOcc 199
  · change (∑ j, (-1 : Int) * x j) ≤ -plane425GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (3 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (13 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (14 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (15 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (21 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (22 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (24 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (38 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (41 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (48 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (49 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (55 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (56 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 56
  · change (∑ k, (if k = (17 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (8 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (47 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_47

end QiushiMatmul
