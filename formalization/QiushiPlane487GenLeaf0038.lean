import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0038Refs : Fin 48 → RowRef 668 48 := ![.occ 86, .occ 95, .occ 111, .occ 186, .occ 224, .occ 227, .occ 237, .occ 240, .occ 241, .occ 263, .occ 296, .occ 312, .occ 313, .occ 314, .occ 315, .occ 325, .occ 338, .occ 356, .occ 367, .occ 376, .occ 378, .occ 386, .occ 415, .occ 421, .occ 433, .occ 468, .occ 476, .occ 521, .occ 523, .occ 542, .occ 546, .occ 589, .occ 605, .occ 633, .occ 639, .occ 641, .occ 650, .occ 665, .sumGe, .nonneg 0, .nonneg 7, .branchLe 39 (0), .branchLe 23 (0), .branchGe 6 (1), .branchGe 33 (1), .branchGe 12 (1), .branchGe 19 (1), .branchGe 22 (1)]

def plane487GenLeaf0038Mult : Fin 48 → Nat := ![2354, 1806, 560, 2018, 2831, 2463, 849, 2466, 2386, 260, 5207, 328, 2355, 2352, 392, 5506, 4928, 212, 2451, 1423, 418, 32, 2704, 2210, 133, 270, 4957, 180, 319, 180, 212, 2953, 2692, 360, 2785, 3038, 2695, 2471, 11215, 821, 1022, 1461, 2631, 18820, 22939, 22108, 18099, 36983]

theorem plane487GenLeaf0038 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_33 : (1 : Int) ≤ x 33)
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0038Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0038Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0038Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0038Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 86
  · exact hroot.hOcc 95
  · exact hroot.hOcc 111
  · exact hroot.hOcc 186
  · exact hroot.hOcc 224
  · exact hroot.hOcc 227
  · exact hroot.hOcc 237
  · exact hroot.hOcc 240
  · exact hroot.hOcc 241
  · exact hroot.hOcc 263
  · exact hroot.hOcc 296
  · exact hroot.hOcc 312
  · exact hroot.hOcc 313
  · exact hroot.hOcc 314
  · exact hroot.hOcc 315
  · exact hroot.hOcc 325
  · exact hroot.hOcc 338
  · exact hroot.hOcc 356
  · exact hroot.hOcc 367
  · exact hroot.hOcc 376
  · exact hroot.hOcc 378
  · exact hroot.hOcc 386
  · exact hroot.hOcc 415
  · exact hroot.hOcc 421
  · exact hroot.hOcc 433
  · exact hroot.hOcc 468
  · exact hroot.hOcc 476
  · exact hroot.hOcc 521
  · exact hroot.hOcc 523
  · exact hroot.hOcc 542
  · exact hroot.hOcc 546
  · exact hroot.hOcc 589
  · exact hroot.hOcc 605
  · exact hroot.hOcc 633
  · exact hroot.hOcc 639
  · exact hroot.hOcc 641
  · exact hroot.hOcc 650
  · exact hroot.hOcc 665
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (7 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (6 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (33 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_33
  · change (∑ k, (if k = (12 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (19 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (22 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22

end QiushiMatmul
