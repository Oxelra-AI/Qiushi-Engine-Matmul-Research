import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0023Refs : Fin 49 → RowRef 668 48 := ![.occ 82, .occ 102, .occ 111, .occ 217, .occ 218, .occ 231, .occ 237, .occ 240, .occ 245, .occ 253, .occ 269, .occ 294, .occ 295, .occ 300, .occ 303, .occ 313, .occ 334, .occ 350, .occ 378, .occ 381, .occ 386, .occ 400, .occ 406, .occ 415, .occ 418, .occ 450, .occ 459, .occ 461, .occ 471, .occ 491, .occ 528, .occ 563, .occ 604, .occ 634, .occ 639, .occ 650, .occ 662, .occ 665, .sumGe, .nonneg 0, .branchLe 39 (0), .branchLe 23 (0), .branchGe 6 (1), .branchLe 33 (0), .branchLe 14 (0), .branchLe 29 (0), .branchLe 44 (0), .branchLe 25 (0), .branchGe 22 (1)]

def plane487GenLeaf0023Mult : Fin 49 → Nat := ![151447, 210497, 333699, 103325, 44602, 152209, 133135, 165144, 12376, 100961, 132777, 141518, 112353, 154621, 276801, 42089, 95985, 136178, 30906, 119064, 128712, 103467, 5824, 109618, 82045, 19401, 27249, 78993, 98974, 69949, 151053, 9865, 17384, 132244, 115591, 176840, 7284, 47182, 723525, 186246, 482354, 520441, 1063313, 669059, 226973, 264488, 461544, 656942, 1039263]

theorem plane487GenLeaf0023 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0023Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0023Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0023Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0023Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 82
  · exact hroot.hOcc 102
  · exact hroot.hOcc 111
  · exact hroot.hOcc 217
  · exact hroot.hOcc 218
  · exact hroot.hOcc 231
  · exact hroot.hOcc 237
  · exact hroot.hOcc 240
  · exact hroot.hOcc 245
  · exact hroot.hOcc 253
  · exact hroot.hOcc 269
  · exact hroot.hOcc 294
  · exact hroot.hOcc 295
  · exact hroot.hOcc 300
  · exact hroot.hOcc 303
  · exact hroot.hOcc 313
  · exact hroot.hOcc 334
  · exact hroot.hOcc 350
  · exact hroot.hOcc 378
  · exact hroot.hOcc 381
  · exact hroot.hOcc 386
  · exact hroot.hOcc 400
  · exact hroot.hOcc 406
  · exact hroot.hOcc 415
  · exact hroot.hOcc 418
  · exact hroot.hOcc 450
  · exact hroot.hOcc 459
  · exact hroot.hOcc 461
  · exact hroot.hOcc 471
  · exact hroot.hOcc 491
  · exact hroot.hOcc 528
  · exact hroot.hOcc 563
  · exact hroot.hOcc 604
  · exact hroot.hOcc 634
  · exact hroot.hOcc 639
  · exact hroot.hOcc 650
  · exact hroot.hOcc 662
  · exact hroot.hOcc 665
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (6 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (33 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (14 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (29 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (44 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (25 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (22 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22

end QiushiMatmul
