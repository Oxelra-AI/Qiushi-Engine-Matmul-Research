import QiushiPlane463GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane463GenLeaf0012Refs : Fin 63 → RowRef 278 63 := ![.occ 2, .occ 10, .occ 11, .occ 14, .occ 16, .occ 38, .occ 46, .occ 50, .occ 54, .occ 62, .occ 69, .occ 79, .occ 81, .occ 98, .occ 105, .occ 117, .occ 125, .occ 132, .occ 141, .occ 144, .occ 145, .occ 148, .occ 149, .occ 157, .occ 159, .occ 160, .occ 164, .occ 167, .occ 169, .occ 175, .occ 186, .occ 196, .occ 202, .occ 221, .occ 225, .occ 231, .occ 244, .occ 246, .occ 249, .occ 255, .occ 268, .occ 271, .occ 272, .occ 274, .sumGe, .nonneg 0, .nonneg 10, .nonneg 11, .nonneg 13, .nonneg 14, .nonneg 28, .nonneg 37, .nonneg 38, .nonneg 40, .nonneg 41, .nonneg 44, .nonneg 49, .nonneg 52, .nonneg 55, .nonneg 61, .branchGe 15 (1), .branchLe 23 (0), .branchGe 33 (1)]

def plane463GenLeaf0012Mult : Fin 63 → Nat := ![1118, 627, 2319, 175, 5658, 956, 1796, 1618, 2868, 351, 36, 1308, 782, 3227, 1426, 783, 314, 356, 893, 452, 291, 541, 99, 2098, 686, 268, 108, 1679, 1015, 1172, 657, 2612, 3398, 3487, 334, 4132, 1270, 1267, 816, 4303, 130, 2909, 41, 1312, 8968, 2968, 8663, 1334, 163, 1459, 416, 1421, 2363, 6650, 1702, 829, 13792, 1622, 1560, 347, 28250, 3111, 32028]

theorem plane463GenLeaf0012 (x : Fin 63 → Int)
    (hroot : plane463GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_33 : (1 : Int) ≤ x 33)
    (hUB_23 : x 23 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane463GenLeaf0012Refs i).resolveCoeff plane463GenOccSys j)
    (fun i => (plane463GenLeaf0012Refs i).resolveRhs plane463GenOccSys) plane463GenLeaf0012Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane463GenLeaf0012Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · exact hroot.hOcc 10
  · exact hroot.hOcc 11
  · exact hroot.hOcc 14
  · exact hroot.hOcc 16
  · exact hroot.hOcc 38
  · exact hroot.hOcc 46
  · exact hroot.hOcc 50
  · exact hroot.hOcc 54
  · exact hroot.hOcc 62
  · exact hroot.hOcc 69
  · exact hroot.hOcc 79
  · exact hroot.hOcc 81
  · exact hroot.hOcc 98
  · exact hroot.hOcc 105
  · exact hroot.hOcc 117
  · exact hroot.hOcc 125
  · exact hroot.hOcc 132
  · exact hroot.hOcc 141
  · exact hroot.hOcc 144
  · exact hroot.hOcc 145
  · exact hroot.hOcc 148
  · exact hroot.hOcc 149
  · exact hroot.hOcc 157
  · exact hroot.hOcc 159
  · exact hroot.hOcc 160
  · exact hroot.hOcc 164
  · exact hroot.hOcc 167
  · exact hroot.hOcc 169
  · exact hroot.hOcc 175
  · exact hroot.hOcc 186
  · exact hroot.hOcc 196
  · exact hroot.hOcc 202
  · exact hroot.hOcc 221
  · exact hroot.hOcc 225
  · exact hroot.hOcc 231
  · exact hroot.hOcc 244
  · exact hroot.hOcc 246
  · exact hroot.hOcc 249
  · exact hroot.hOcc 255
  · exact hroot.hOcc 268
  · exact hroot.hOcc 271
  · exact hroot.hOcc 272
  · exact hroot.hOcc 274
  · change (∑ j, (-1 : Int) * x j) ≤ -plane463GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (10 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (11 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (13 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (14 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (28 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (37 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (38 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (40 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (41 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (44 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (49 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (52 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (55 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (61 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 61
  · change (∑ k, (if k = (15 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (23 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (33 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_33

end QiushiMatmul
