import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0108Refs : Fin 50 → RowRef 726 49 := ![.occ 106, .occ 109, .occ 110, .occ 112, .occ 171, .occ 197, .occ 299, .occ 305, .occ 319, .occ 323, .occ 332, .occ 338, .occ 344, .occ 349, .occ 355, .occ 363, .occ 404, .occ 422, .occ 425, .occ 440, .occ 443, .occ 469, .occ 495, .occ 531, .occ 538, .occ 551, .occ 566, .occ 575, .occ 582, .occ 601, .occ 611, .occ 622, .occ 626, .occ 648, .occ 661, .occ 662, .occ 665, .occ 691, .occ 709, .occ 716, .occ 722, .occ 723, .sumGe, .nonneg 41, .nonneg 45, .branchGe 31 (1), .branchGe 44 (1), .branchLe 6 (0), .branchGe 39 (1), .branchGe 27 (1)]

def plane491GenLeaf0108Mult : Fin 50 → Nat := ![2808, 4360, 11, 14514, 4092, 5082, 136, 484, 582, 636, 310, 5412, 13495, 872, 3031, 2385, 639, 1610, 737, 8060, 1735, 2415, 6611, 892, 3419, 236, 992, 49, 758, 15826, 1988, 1590, 253, 6421, 1406, 429, 3670, 378, 7011, 3969, 2175, 185, 19456, 724, 2589, 69276, 32891, 11047, 66820, 57294]

theorem plane491GenLeaf0108 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_44 : (1 : Int) ≤ x 44)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_6 : x 6 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0108Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0108Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0108Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0108Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 106
  · exact hroot.hOcc 109
  · exact hroot.hOcc 110
  · exact hroot.hOcc 112
  · exact hroot.hOcc 171
  · exact hroot.hOcc 197
  · exact hroot.hOcc 299
  · exact hroot.hOcc 305
  · exact hroot.hOcc 319
  · exact hroot.hOcc 323
  · exact hroot.hOcc 332
  · exact hroot.hOcc 338
  · exact hroot.hOcc 344
  · exact hroot.hOcc 349
  · exact hroot.hOcc 355
  · exact hroot.hOcc 363
  · exact hroot.hOcc 404
  · exact hroot.hOcc 422
  · exact hroot.hOcc 425
  · exact hroot.hOcc 440
  · exact hroot.hOcc 443
  · exact hroot.hOcc 469
  · exact hroot.hOcc 495
  · exact hroot.hOcc 531
  · exact hroot.hOcc 538
  · exact hroot.hOcc 551
  · exact hroot.hOcc 566
  · exact hroot.hOcc 575
  · exact hroot.hOcc 582
  · exact hroot.hOcc 601
  · exact hroot.hOcc 611
  · exact hroot.hOcc 622
  · exact hroot.hOcc 626
  · exact hroot.hOcc 648
  · exact hroot.hOcc 661
  · exact hroot.hOcc 662
  · exact hroot.hOcc 665
  · exact hroot.hOcc 691
  · exact hroot.hOcc 709
  · exact hroot.hOcc 716
  · exact hroot.hOcc 722
  · exact hroot.hOcc 723
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (41 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (45 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_44
  · change (∑ k, (if k = (6 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (39 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (27 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27

end QiushiMatmul
