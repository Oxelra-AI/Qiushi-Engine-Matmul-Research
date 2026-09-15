import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0062Refs : Fin 49 → RowRef 668 48 := ![.occ 82, .occ 90, .occ 99, .occ 108, .occ 110, .occ 162, .occ 167, .occ 219, .occ 223, .occ 225, .occ 226, .occ 231, .occ 246, .occ 253, .occ 260, .occ 295, .occ 296, .occ 303, .occ 306, .occ 308, .occ 315, .occ 335, .occ 340, .occ 343, .occ 347, .occ 381, .occ 386, .occ 390, .occ 391, .occ 399, .occ 470, .occ 471, .occ 491, .occ 526, .occ 588, .occ 614, .occ 650, .occ 664, .sumGe, .nonneg 0, .nonneg 7, .nonneg 12, .branchGe 39 (1), .branchLe 28 (0), .branchLe 40 (0), .branchLe 29 (0), .branchLe 19 (0), .branchGe 36 (1), .branchLe 37 (0)]

def plane487GenLeaf0062Mult : Fin 49 → Nat := ![13886, 46880, 106800, 84838, 565, 40984, 7171, 70378, 6568, 75935, 22064, 2026, 27098, 696, 3110, 1453, 31229, 81312, 64705, 56126, 36171, 5100, 124497, 112845, 3110, 73488, 15830, 21917, 573, 68907, 57755, 34182, 17798, 6757, 52007, 8210, 69028, 2073, 232843, 2843, 8790, 8858, 75090, 217013, 47439, 161863, 190104, 614214, 96534]

theorem plane487GenLeaf0062 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0062Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0062Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0062Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0062Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 82
  · exact hroot.hOcc 90
  · exact hroot.hOcc 99
  · exact hroot.hOcc 108
  · exact hroot.hOcc 110
  · exact hroot.hOcc 162
  · exact hroot.hOcc 167
  · exact hroot.hOcc 219
  · exact hroot.hOcc 223
  · exact hroot.hOcc 225
  · exact hroot.hOcc 226
  · exact hroot.hOcc 231
  · exact hroot.hOcc 246
  · exact hroot.hOcc 253
  · exact hroot.hOcc 260
  · exact hroot.hOcc 295
  · exact hroot.hOcc 296
  · exact hroot.hOcc 303
  · exact hroot.hOcc 306
  · exact hroot.hOcc 308
  · exact hroot.hOcc 315
  · exact hroot.hOcc 335
  · exact hroot.hOcc 340
  · exact hroot.hOcc 343
  · exact hroot.hOcc 347
  · exact hroot.hOcc 381
  · exact hroot.hOcc 386
  · exact hroot.hOcc 390
  · exact hroot.hOcc 391
  · exact hroot.hOcc 399
  · exact hroot.hOcc 470
  · exact hroot.hOcc 471
  · exact hroot.hOcc 491
  · exact hroot.hOcc 526
  · exact hroot.hOcc 588
  · exact hroot.hOcc 614
  · exact hroot.hOcc 650
  · exact hroot.hOcc 664
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (7 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (12 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (28 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (40 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (29 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (19 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (36 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36
  · change (∑ k, (if k = (37 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37

end QiushiMatmul
