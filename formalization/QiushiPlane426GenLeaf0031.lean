import QiushiPlane426GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane426GenLeaf0031Refs : Fin 58 → RowRef 340 58 := ![.occ 16, .occ 17, .occ 22, .occ 27, .occ 29, .occ 35, .occ 44, .occ 68, .occ 72, .occ 76, .occ 81, .occ 86, .occ 103, .occ 109, .occ 113, .occ 123, .occ 125, .occ 134, .occ 135, .occ 144, .occ 149, .occ 150, .occ 153, .occ 160, .occ 163, .occ 191, .occ 205, .occ 206, .occ 208, .occ 243, .occ 244, .occ 258, .occ 289, .occ 295, .occ 298, .occ 309, .occ 313, .occ 314, .occ 317, .occ 319, .occ 330, .occ 334, .occ 335, .sumGe, .nonneg 16, .nonneg 17, .nonneg 23, .nonneg 25, .nonneg 30, .nonneg 33, .nonneg 36, .nonneg 40, .nonneg 44, .nonneg 46, .nonneg 47, .branchLe 43 (0), .branchGe 14 (1), .branchGe 42 (1)]

def plane426GenLeaf0031Mult : Fin 58 → Nat := ![792, 206, 594, 306, 214, 188, 114, 36, 334, 156, 66, 48, 150, 228, 204, 84, 514, 48, 42, 156, 114, 6, 72, 478, 484, 108, 2, 53, 33, 9, 51, 60, 18, 42, 132, 149, 375, 198, 143, 161, 234, 236, 147, 939, 264, 2528, 250, 96, 104, 294, 154, 214, 342, 132, 496, 412, 1018, 4350]

theorem plane426GenLeaf0031 (x : Fin 58 → Int)
    (hroot : plane426GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hUB_43 : x 43 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane426GenLeaf0031Refs i).resolveCoeff plane426GenOccSys j)
    (fun i => (plane426GenLeaf0031Refs i).resolveRhs plane426GenOccSys) plane426GenLeaf0031Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane426GenLeaf0031Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 16
  · exact hroot.hOcc 17
  · exact hroot.hOcc 22
  · exact hroot.hOcc 27
  · exact hroot.hOcc 29
  · exact hroot.hOcc 35
  · exact hroot.hOcc 44
  · exact hroot.hOcc 68
  · exact hroot.hOcc 72
  · exact hroot.hOcc 76
  · exact hroot.hOcc 81
  · exact hroot.hOcc 86
  · exact hroot.hOcc 103
  · exact hroot.hOcc 109
  · exact hroot.hOcc 113
  · exact hroot.hOcc 123
  · exact hroot.hOcc 125
  · exact hroot.hOcc 134
  · exact hroot.hOcc 135
  · exact hroot.hOcc 144
  · exact hroot.hOcc 149
  · exact hroot.hOcc 150
  · exact hroot.hOcc 153
  · exact hroot.hOcc 160
  · exact hroot.hOcc 163
  · exact hroot.hOcc 191
  · exact hroot.hOcc 205
  · exact hroot.hOcc 206
  · exact hroot.hOcc 208
  · exact hroot.hOcc 243
  · exact hroot.hOcc 244
  · exact hroot.hOcc 258
  · exact hroot.hOcc 289
  · exact hroot.hOcc 295
  · exact hroot.hOcc 298
  · exact hroot.hOcc 309
  · exact hroot.hOcc 313
  · exact hroot.hOcc 314
  · exact hroot.hOcc 317
  · exact hroot.hOcc 319
  · exact hroot.hOcc 330
  · exact hroot.hOcc 334
  · exact hroot.hOcc 335
  · change (∑ j, (-1 : Int) * x j) ≤ -plane426GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (16 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (23 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (25 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (30 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (33 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (36 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (40 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (44 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (46 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (47 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (43 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (14 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (42 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42

end QiushiMatmul
