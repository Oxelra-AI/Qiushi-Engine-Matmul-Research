import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0110Refs : Fin 50 → RowRef 726 49 := ![.occ 81, .occ 105, .occ 112, .occ 119, .occ 177, .occ 200, .occ 211, .occ 234, .occ 248, .occ 253, .occ 255, .occ 257, .occ 258, .occ 292, .occ 296, .occ 305, .occ 318, .occ 329, .occ 332, .occ 355, .occ 363, .occ 365, .occ 394, .occ 421, .occ 425, .occ 431, .occ 451, .occ 495, .occ 509, .occ 570, .occ 571, .occ 582, .occ 632, .occ 652, .occ 655, .occ 662, .occ 673, .occ 718, .occ 723, .sumGe, .nonneg 24, .nonneg 32, .nonneg 33, .branchGe 31 (1), .branchGe 44 (1), .branchGe 6 (1), .branchLe 15 (0), .branchLe 9 (0), .branchLe 14 (0), .branchGe 36 (1)]

def plane491GenLeaf0110Mult : Fin 50 → Nat := ![9871, 64376, 27925, 32172, 63078, 20163, 25762, 21364, 20446, 18615, 51837, 3679, 15437, 28564, 418, 19440, 6164, 34940, 22343, 8961, 58879, 4713, 3300, 24166, 25399, 4189, 5766, 15878, 24253, 5348, 3898, 667, 10475, 40348, 8464, 17566, 5052, 1021, 21648, 98320, 7005, 34184, 60635, 87218, 236764, 152235, 80754, 52703, 76672, 317950]

theorem plane491GenLeaf0110 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_44 : (1 : Int) ≤ x 44)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0110Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0110Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0110Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0110Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 81
  · exact hroot.hOcc 105
  · exact hroot.hOcc 112
  · exact hroot.hOcc 119
  · exact hroot.hOcc 177
  · exact hroot.hOcc 200
  · exact hroot.hOcc 211
  · exact hroot.hOcc 234
  · exact hroot.hOcc 248
  · exact hroot.hOcc 253
  · exact hroot.hOcc 255
  · exact hroot.hOcc 257
  · exact hroot.hOcc 258
  · exact hroot.hOcc 292
  · exact hroot.hOcc 296
  · exact hroot.hOcc 305
  · exact hroot.hOcc 318
  · exact hroot.hOcc 329
  · exact hroot.hOcc 332
  · exact hroot.hOcc 355
  · exact hroot.hOcc 363
  · exact hroot.hOcc 365
  · exact hroot.hOcc 394
  · exact hroot.hOcc 421
  · exact hroot.hOcc 425
  · exact hroot.hOcc 431
  · exact hroot.hOcc 451
  · exact hroot.hOcc 495
  · exact hroot.hOcc 509
  · exact hroot.hOcc 570
  · exact hroot.hOcc 571
  · exact hroot.hOcc 582
  · exact hroot.hOcc 632
  · exact hroot.hOcc 652
  · exact hroot.hOcc 655
  · exact hroot.hOcc 662
  · exact hroot.hOcc 673
  · exact hroot.hOcc 718
  · exact hroot.hOcc 723
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (24 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (32 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (33 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_44
  · change (∑ k, (if k = (6 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (15 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (9 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (14 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (36 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36

end QiushiMatmul
