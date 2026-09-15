import QiushiPlane466GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane466GenLeaf0003Refs : Fin 51 → RowRef 210 50 := ![.occ 18, .occ 21, .occ 29, .occ 34, .occ 51, .occ 78, .occ 79, .occ 91, .occ 100, .occ 101, .occ 102, .occ 107, .occ 108, .occ 111, .occ 113, .occ 120, .occ 123, .occ 124, .occ 126, .occ 127, .occ 133, .occ 135, .occ 137, .occ 138, .occ 139, .occ 141, .occ 147, .occ 148, .occ 155, .occ 159, .occ 160, .occ 175, .occ 180, .occ 185, .occ 198, .occ 204, .occ 206, .sumGe, .nonneg 0, .nonneg 14, .nonneg 16, .nonneg 18, .nonneg 32, .nonneg 36, .nonneg 40, .nonneg 42, .nonneg 44, .nonneg 48, .branchLe 24 (0), .branchLe 19 (0), .branchGe 26 (1)]

def plane466GenLeaf0003Mult : Fin 51 → Nat := ![3400, 2940, 1834, 11165, 7495, 10329, 4441, 3288, 3966, 4346, 5346, 598, 7102, 5759, 5669, 7534, 601, 5376, 4095, 569, 2266, 665, 1227, 1320, 4063, 169, 866, 1270, 8989, 2591, 1752, 3553, 114, 1302, 2667, 2476, 3319, 18301, 9393, 11883, 3293, 9977, 171, 873, 963, 7711, 3778, 7275, 6879, 13955, 71171]

theorem plane466GenLeaf0003 (x : Fin 50 → Int)
    (hroot : plane466GenOccSys.RootHolds x)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane466GenLeaf0003Refs i).resolveCoeff plane466GenOccSys j)
    (fun i => (plane466GenLeaf0003Refs i).resolveRhs plane466GenOccSys) plane466GenLeaf0003Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane466GenLeaf0003Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 18
  · exact hroot.hOcc 21
  · exact hroot.hOcc 29
  · exact hroot.hOcc 34
  · exact hroot.hOcc 51
  · exact hroot.hOcc 78
  · exact hroot.hOcc 79
  · exact hroot.hOcc 91
  · exact hroot.hOcc 100
  · exact hroot.hOcc 101
  · exact hroot.hOcc 102
  · exact hroot.hOcc 107
  · exact hroot.hOcc 108
  · exact hroot.hOcc 111
  · exact hroot.hOcc 113
  · exact hroot.hOcc 120
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 126
  · exact hroot.hOcc 127
  · exact hroot.hOcc 133
  · exact hroot.hOcc 135
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 139
  · exact hroot.hOcc 141
  · exact hroot.hOcc 147
  · exact hroot.hOcc 148
  · exact hroot.hOcc 155
  · exact hroot.hOcc 159
  · exact hroot.hOcc 160
  · exact hroot.hOcc 175
  · exact hroot.hOcc 180
  · exact hroot.hOcc 185
  · exact hroot.hOcc 198
  · exact hroot.hOcc 204
  · exact hroot.hOcc 206
  · change (∑ j, (-1 : Int) * x j) ≤ -plane466GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (14 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (16 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (18 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (32 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (36 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (40 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (42 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (44 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (48 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (24 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (19 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (26 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26

end QiushiMatmul
