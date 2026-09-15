import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0035Refs : Fin 50 → RowRef 726 49 := ![.occ 85, .occ 89, .occ 94, .occ 97, .occ 116, .occ 145, .occ 237, .occ 255, .occ 257, .occ 304, .occ 324, .occ 329, .occ 351, .occ 355, .occ 364, .occ 389, .occ 392, .occ 400, .occ 402, .occ 410, .occ 415, .occ 420, .occ 422, .occ 430, .occ 474, .occ 501, .occ 506, .occ 517, .occ 550, .occ 552, .occ 581, .occ 584, .occ 594, .occ 628, .occ 642, .occ 665, .occ 673, .occ 713, .occ 718, .sumGe, .nonneg 10, .nonneg 44, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchGe 29 (1), .branchLe 43 (0), .branchLe 9 (0), .branchLe 5 (0), .branchGe 24 (1)]

def plane491GenLeaf0035Mult : Fin 50 → Nat := ![26300, 98818, 32712, 19543, 14756, 35642, 33078, 3020, 11212, 18388, 9913, 4893, 2100, 21883, 14839, 11332, 38185, 15804, 40630, 1794, 11035, 16119, 25835, 69289, 13178, 345, 16846, 8242, 42517, 13268, 2178, 13258, 33743, 3933, 3790, 3467, 4521, 6236, 37075, 111944, 38473, 16158, 62079, 52418, 49656, 247442, 78201, 98676, 22682, 392975]

theorem plane491GenLeaf0035 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_43 : x 43 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0035Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0035Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0035Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0035Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 85
  · exact hroot.hOcc 89
  · exact hroot.hOcc 94
  · exact hroot.hOcc 97
  · exact hroot.hOcc 116
  · exact hroot.hOcc 145
  · exact hroot.hOcc 237
  · exact hroot.hOcc 255
  · exact hroot.hOcc 257
  · exact hroot.hOcc 304
  · exact hroot.hOcc 324
  · exact hroot.hOcc 329
  · exact hroot.hOcc 351
  · exact hroot.hOcc 355
  · exact hroot.hOcc 364
  · exact hroot.hOcc 389
  · exact hroot.hOcc 392
  · exact hroot.hOcc 400
  · exact hroot.hOcc 402
  · exact hroot.hOcc 410
  · exact hroot.hOcc 415
  · exact hroot.hOcc 420
  · exact hroot.hOcc 422
  · exact hroot.hOcc 430
  · exact hroot.hOcc 474
  · exact hroot.hOcc 501
  · exact hroot.hOcc 506
  · exact hroot.hOcc 517
  · exact hroot.hOcc 550
  · exact hroot.hOcc 552
  · exact hroot.hOcc 581
  · exact hroot.hOcc 584
  · exact hroot.hOcc 594
  · exact hroot.hOcc 628
  · exact hroot.hOcc 642
  · exact hroot.hOcc 665
  · exact hroot.hOcc 673
  · exact hroot.hOcc 713
  · exact hroot.hOcc 718
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (44 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (43 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (9 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (5 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (24 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24

end QiushiMatmul
