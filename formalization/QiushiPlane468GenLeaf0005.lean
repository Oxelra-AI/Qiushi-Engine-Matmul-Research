import QiushiPlane468GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane468GenLeaf0005Refs : Fin 63 → RowRef 253 62 := ![.occ 2, .occ 3, .occ 5, .occ 18, .occ 26, .occ 29, .occ 48, .occ 69, .occ 73, .occ 79, .occ 84, .occ 104, .occ 105, .occ 107, .occ 112, .occ 124, .occ 130, .occ 135, .occ 139, .occ 143, .occ 159, .occ 163, .occ 167, .occ 169, .occ 171, .occ 173, .occ 175, .occ 184, .occ 197, .occ 198, .occ 199, .occ 200, .occ 204, .occ 205, .occ 209, .occ 214, .occ 221, .occ 226, .occ 227, .occ 230, .occ 236, .occ 237, .occ 239, .occ 242, .occ 247, .occ 248, .occ 249, .occ 250, .occ 251, .sumGe, .nonneg 10, .nonneg 20, .nonneg 30, .nonneg 34, .nonneg 37, .nonneg 39, .nonneg 60, .branchLe 28 (0), .branchGe 51 (1), .branchLe 15 (0), .branchGe 2 (1), .branchLe 1 (0), .branchLe 49 (0)]

def plane468GenLeaf0005Mult : Fin 63 → Nat := ![337344, 110874, 305674, 671740, 354520, 205698, 915710, 1191872, 1963364, 671616, 1422790, 4944600, 277306, 1912974, 860972, 3583520, 1317334, 4655674, 2181138, 1251992, 1341753, 2141231, 1005948, 714517, 892063, 1132560, 999302, 1991876, 1901462, 732399, 149764, 591890, 481320, 176350, 1956829, 1404042, 1217276, 601929, 598584, 1638754, 1405592, 1707874, 312067, 973988, 235258, 1283946, 771105, 470261, 406750, 11138348, 370406, 5585344, 5459738, 984156, 4031696, 4117312, 8297722, 8771230, 12575358, 4930048, 7928716, 11138348, 8836816]

theorem plane468GenLeaf0005 (x : Fin 62 → Int)
    (hroot : plane468GenOccSys.RootHolds x)
    (hLB_51 : (1 : Int) ≤ x 51)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_49 : x 49 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane468GenLeaf0005Refs i).resolveCoeff plane468GenOccSys j)
    (fun i => (plane468GenLeaf0005Refs i).resolveRhs plane468GenOccSys) plane468GenLeaf0005Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane468GenLeaf0005Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · exact hroot.hOcc 3
  · exact hroot.hOcc 5
  · exact hroot.hOcc 18
  · exact hroot.hOcc 26
  · exact hroot.hOcc 29
  · exact hroot.hOcc 48
  · exact hroot.hOcc 69
  · exact hroot.hOcc 73
  · exact hroot.hOcc 79
  · exact hroot.hOcc 84
  · exact hroot.hOcc 104
  · exact hroot.hOcc 105
  · exact hroot.hOcc 107
  · exact hroot.hOcc 112
  · exact hroot.hOcc 124
  · exact hroot.hOcc 130
  · exact hroot.hOcc 135
  · exact hroot.hOcc 139
  · exact hroot.hOcc 143
  · exact hroot.hOcc 159
  · exact hroot.hOcc 163
  · exact hroot.hOcc 167
  · exact hroot.hOcc 169
  · exact hroot.hOcc 171
  · exact hroot.hOcc 173
  · exact hroot.hOcc 175
  · exact hroot.hOcc 184
  · exact hroot.hOcc 197
  · exact hroot.hOcc 198
  · exact hroot.hOcc 199
  · exact hroot.hOcc 200
  · exact hroot.hOcc 204
  · exact hroot.hOcc 205
  · exact hroot.hOcc 209
  · exact hroot.hOcc 214
  · exact hroot.hOcc 221
  · exact hroot.hOcc 226
  · exact hroot.hOcc 227
  · exact hroot.hOcc 230
  · exact hroot.hOcc 236
  · exact hroot.hOcc 237
  · exact hroot.hOcc 239
  · exact hroot.hOcc 242
  · exact hroot.hOcc 247
  · exact hroot.hOcc 248
  · exact hroot.hOcc 249
  · exact hroot.hOcc 250
  · exact hroot.hOcc 251
  · change (∑ j, (-1 : Int) * x j) ≤ -plane468GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (20 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (30 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (34 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 34
  · change (∑ k, (if k = (37 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (39 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (60 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 60
  · change (∑ k, (if k = (28 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (51 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_51
  · change (∑ k, (if k = (15 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (1 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (49 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_49

end QiushiMatmul
