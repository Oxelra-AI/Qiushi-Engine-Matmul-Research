import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0084Refs : Fin 48 → RowRef 668 48 := ![.occ 85, .occ 105, .occ 164, .occ 196, .occ 237, .occ 240, .occ 243, .occ 246, .occ 253, .occ 263, .occ 296, .occ 303, .occ 306, .occ 308, .occ 315, .occ 332, .occ 343, .occ 345, .occ 349, .occ 352, .occ 354, .occ 358, .occ 359, .occ 365, .occ 386, .occ 399, .occ 471, .occ 491, .occ 492, .occ 511, .occ 526, .occ 539, .occ 577, .occ 581, .occ 598, .occ 655, .occ 661, .occ 662, .occ 665, .sumGe, .nonneg 7, .nonneg 8, .nonneg 32, .nonneg 40, .branchGe 39 (1), .branchGe 28 (1), .branchLe 3 (0), .branchGe 36 (1)]

def plane487GenLeaf0084Mult : Fin 48 → Nat := ![425, 12088, 15445, 7652, 4552, 7996, 8527, 4286, 6680, 108, 8710, 5182, 2596, 2542, 6137, 7926, 812, 4893, 9018, 9300, 7399, 5978, 8905, 1493, 8075, 4286, 1734, 1713, 839, 62, 5277, 1637, 1007, 1039, 5251, 5185, 3962, 69, 3785, 25994, 10654, 6047, 1085, 2174, 30209, 89908, 18206, 79622]

theorem plane487GenLeaf0084 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0084Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0084Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0084Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0084Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 85
  · exact hroot.hOcc 105
  · exact hroot.hOcc 164
  · exact hroot.hOcc 196
  · exact hroot.hOcc 237
  · exact hroot.hOcc 240
  · exact hroot.hOcc 243
  · exact hroot.hOcc 246
  · exact hroot.hOcc 253
  · exact hroot.hOcc 263
  · exact hroot.hOcc 296
  · exact hroot.hOcc 303
  · exact hroot.hOcc 306
  · exact hroot.hOcc 308
  · exact hroot.hOcc 315
  · exact hroot.hOcc 332
  · exact hroot.hOcc 343
  · exact hroot.hOcc 345
  · exact hroot.hOcc 349
  · exact hroot.hOcc 352
  · exact hroot.hOcc 354
  · exact hroot.hOcc 358
  · exact hroot.hOcc 359
  · exact hroot.hOcc 365
  · exact hroot.hOcc 386
  · exact hroot.hOcc 399
  · exact hroot.hOcc 471
  · exact hroot.hOcc 491
  · exact hroot.hOcc 492
  · exact hroot.hOcc 511
  · exact hroot.hOcc 526
  · exact hroot.hOcc 539
  · exact hroot.hOcc 577
  · exact hroot.hOcc 581
  · exact hroot.hOcc 598
  · exact hroot.hOcc 655
  · exact hroot.hOcc 661
  · exact hroot.hOcc 662
  · exact hroot.hOcc 665
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (8 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (32 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (40 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (28 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (3 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (36 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36

end QiushiMatmul
