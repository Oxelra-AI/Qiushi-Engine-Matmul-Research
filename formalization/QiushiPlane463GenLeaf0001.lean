import QiushiPlane463GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane463GenLeaf0001Refs : Fin 64 → RowRef 278 63 := ![.occ 8, .occ 12, .occ 13, .occ 15, .occ 20, .occ 36, .occ 44, .occ 45, .occ 49, .occ 52, .occ 56, .occ 74, .occ 79, .occ 94, .occ 95, .occ 111, .occ 114, .occ 119, .occ 127, .occ 129, .occ 151, .occ 154, .occ 168, .occ 173, .occ 175, .occ 179, .occ 181, .occ 186, .occ 194, .occ 214, .occ 222, .occ 229, .occ 230, .occ 233, .occ 236, .occ 244, .occ 245, .occ 246, .occ 247, .occ 259, .occ 266, .occ 268, .occ 272, .occ 276, .sumGe, .nonneg 0, .nonneg 10, .nonneg 11, .nonneg 37, .nonneg 40, .nonneg 41, .nonneg 42, .nonneg 49, .nonneg 59, .branchLe 15 (0), .branchLe 24 (0), .branchLe 60 (0), .branchLe 21 (0), .branchLe 19 (0), .branchLe 47 (0), .branchLe 22 (0), .branchLe 20 (0), .branchLe 2 (0), .branchGe 29 (1)]

def plane463GenLeaf0001Mult : Fin 64 → Nat := ![28280, 87759, 18586, 44152, 133920, 89785, 272865, 12942, 107496, 246485, 24941, 57338, 149765, 55807, 1646, 115356, 30300, 79138, 55440, 69946, 13226, 100406, 18382, 59917, 17773, 14835, 21200, 58312, 76771, 6286, 83323, 63472, 24014, 16972, 998, 50453, 11110, 6494, 2827, 10881, 64372, 39388, 21235, 81775, 349345, 361397, 28183, 10106, 184458, 220024, 30747, 74717, 140890, 25381, 261076, 328110, 94477, 318997, 177594, 261076, 235445, 134533, 96570, 1012899]

theorem plane463GenLeaf0001 (x : Fin 63 → Int)
    (hroot : plane463GenOccSys.RootHolds x)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_60 : x 60 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_47 : x 47 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane463GenLeaf0001Refs i).resolveCoeff plane463GenOccSys j)
    (fun i => (plane463GenLeaf0001Refs i).resolveRhs plane463GenOccSys) plane463GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane463GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 8
  · exact hroot.hOcc 12
  · exact hroot.hOcc 13
  · exact hroot.hOcc 15
  · exact hroot.hOcc 20
  · exact hroot.hOcc 36
  · exact hroot.hOcc 44
  · exact hroot.hOcc 45
  · exact hroot.hOcc 49
  · exact hroot.hOcc 52
  · exact hroot.hOcc 56
  · exact hroot.hOcc 74
  · exact hroot.hOcc 79
  · exact hroot.hOcc 94
  · exact hroot.hOcc 95
  · exact hroot.hOcc 111
  · exact hroot.hOcc 114
  · exact hroot.hOcc 119
  · exact hroot.hOcc 127
  · exact hroot.hOcc 129
  · exact hroot.hOcc 151
  · exact hroot.hOcc 154
  · exact hroot.hOcc 168
  · exact hroot.hOcc 173
  · exact hroot.hOcc 175
  · exact hroot.hOcc 179
  · exact hroot.hOcc 181
  · exact hroot.hOcc 186
  · exact hroot.hOcc 194
  · exact hroot.hOcc 214
  · exact hroot.hOcc 222
  · exact hroot.hOcc 229
  · exact hroot.hOcc 230
  · exact hroot.hOcc 233
  · exact hroot.hOcc 236
  · exact hroot.hOcc 244
  · exact hroot.hOcc 245
  · exact hroot.hOcc 246
  · exact hroot.hOcc 247
  · exact hroot.hOcc 259
  · exact hroot.hOcc 266
  · exact hroot.hOcc 268
  · exact hroot.hOcc 272
  · exact hroot.hOcc 276
  · change (∑ j, (-1 : Int) * x j) ≤ -plane463GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (10 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (11 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (37 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (40 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (41 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (42 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (49 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (59 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (15 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (24 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (60 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_60
  · change (∑ k, (if k = (21 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (19 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (47 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_47
  · change (∑ k, (if k = (22 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (20 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (2 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29

end QiushiMatmul
