import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0009Refs : Fin 50 → RowRef 726 49 := ![.occ 97, .occ 108, .occ 114, .occ 120, .occ 204, .occ 240, .occ 254, .occ 255, .occ 256, .occ 257, .occ 258, .occ 331, .occ 332, .occ 373, .occ 382, .occ 463, .occ 509, .occ 511, .occ 516, .occ 541, .occ 549, .occ 566, .occ 568, .occ 569, .occ 570, .occ 571, .occ 573, .occ 576, .occ 631, .occ 632, .occ 640, .occ 643, .occ 647, .occ 656, .occ 668, .occ 691, .occ 707, .occ 714, .occ 716, .sumGe, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchLe 29 (0), .branchLe 46 (0), .branchLe 32 (0), .branchLe 38 (0), .branchGe 6 (1), .branchLe 0 (0), .branchGe 43 (1)]

def plane491GenLeaf0009Mult : Fin 50 → Nat := ![230454, 2674034, 1836150, 1123120, 1599079, 796298, 1743452, 698426, 1449852, 96275, 249389, 825729, 360505, 345177, 262205, 713356, 227955, 86585, 900572, 430556, 818792, 203830, 1058578, 612615, 710787, 1359757, 290113, 1350641, 335230, 117914, 433566, 722258, 114418, 177268, 349828, 658733, 398771, 712929, 77137, 5034001, 4319468, 2598419, 3035276, 3157559, 4743888, 4600435, 1876641, 3650986, 4147313, 14776258]

theorem plane491GenLeaf0009 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_43 : (1 : Int) ≤ x 43)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_46 : x 46 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_38 : x 38 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0009Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0009Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0009Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0009Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 97
  · exact hroot.hOcc 108
  · exact hroot.hOcc 114
  · exact hroot.hOcc 120
  · exact hroot.hOcc 204
  · exact hroot.hOcc 240
  · exact hroot.hOcc 254
  · exact hroot.hOcc 255
  · exact hroot.hOcc 256
  · exact hroot.hOcc 257
  · exact hroot.hOcc 258
  · exact hroot.hOcc 331
  · exact hroot.hOcc 332
  · exact hroot.hOcc 373
  · exact hroot.hOcc 382
  · exact hroot.hOcc 463
  · exact hroot.hOcc 509
  · exact hroot.hOcc 511
  · exact hroot.hOcc 516
  · exact hroot.hOcc 541
  · exact hroot.hOcc 549
  · exact hroot.hOcc 566
  · exact hroot.hOcc 568
  · exact hroot.hOcc 569
  · exact hroot.hOcc 570
  · exact hroot.hOcc 571
  · exact hroot.hOcc 573
  · exact hroot.hOcc 576
  · exact hroot.hOcc 631
  · exact hroot.hOcc 632
  · exact hroot.hOcc 640
  · exact hroot.hOcc 643
  · exact hroot.hOcc 647
  · exact hroot.hOcc 656
  · exact hroot.hOcc 668
  · exact hroot.hOcc 691
  · exact hroot.hOcc 707
  · exact hroot.hOcc 714
  · exact hroot.hOcc 716
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (46 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_46
  · change (∑ k, (if k = (32 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (38 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (6 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (0 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (43 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_43

end QiushiMatmul
