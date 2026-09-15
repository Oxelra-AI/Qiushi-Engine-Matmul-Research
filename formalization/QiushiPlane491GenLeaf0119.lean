import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0119Refs : Fin 50 → RowRef 726 49 := ![.occ 81, .occ 98, .occ 105, .occ 112, .occ 118, .occ 135, .occ 155, .occ 170, .occ 195, .occ 217, .occ 221, .occ 255, .occ 267, .occ 295, .occ 305, .occ 320, .occ 329, .occ 335, .occ 350, .occ 363, .occ 377, .occ 378, .occ 383, .occ 388, .occ 393, .occ 423, .occ 523, .occ 568, .occ 570, .occ 580, .occ 585, .occ 586, .occ 592, .occ 631, .occ 640, .occ 643, .occ 652, .occ 653, .occ 654, .occ 662, .occ 701, .sumGe, .nonneg 17, .nonneg 32, .nonneg 47, .branchGe 31 (1), .branchGe 44 (1), .branchGe 6 (1), .branchGe 15 (1), .branchGe 13 (1)]

def plane491GenLeaf0119Mult : Fin 50 → Nat := ![23833, 23350, 2244, 53320, 2619, 19464, 30840, 8052, 387, 4251, 37374, 5811, 956, 4714, 5777, 9370, 22164, 15502, 19793, 12590, 6315, 21569, 9543, 57130, 26956, 25502, 8041, 5004, 21141, 11431, 9067, 5223, 14115, 11906, 41359, 15792, 5111, 4348, 5349, 3413, 9796, 71003, 28348, 22626, 21597, 107316, 212850, 183972, 44367, 316342]

theorem plane491GenLeaf0119 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_44 : (1 : Int) ≤ x 44)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_6 : (1 : Int) ≤ x 6)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0119Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0119Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0119Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0119Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 81
  · exact hroot.hOcc 98
  · exact hroot.hOcc 105
  · exact hroot.hOcc 112
  · exact hroot.hOcc 118
  · exact hroot.hOcc 135
  · exact hroot.hOcc 155
  · exact hroot.hOcc 170
  · exact hroot.hOcc 195
  · exact hroot.hOcc 217
  · exact hroot.hOcc 221
  · exact hroot.hOcc 255
  · exact hroot.hOcc 267
  · exact hroot.hOcc 295
  · exact hroot.hOcc 305
  · exact hroot.hOcc 320
  · exact hroot.hOcc 329
  · exact hroot.hOcc 335
  · exact hroot.hOcc 350
  · exact hroot.hOcc 363
  · exact hroot.hOcc 377
  · exact hroot.hOcc 378
  · exact hroot.hOcc 383
  · exact hroot.hOcc 388
  · exact hroot.hOcc 393
  · exact hroot.hOcc 423
  · exact hroot.hOcc 523
  · exact hroot.hOcc 568
  · exact hroot.hOcc 570
  · exact hroot.hOcc 580
  · exact hroot.hOcc 585
  · exact hroot.hOcc 586
  · exact hroot.hOcc 592
  · exact hroot.hOcc 631
  · exact hroot.hOcc 640
  · exact hroot.hOcc 643
  · exact hroot.hOcc 652
  · exact hroot.hOcc 653
  · exact hroot.hOcc 654
  · exact hroot.hOcc 662
  · exact hroot.hOcc 701
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (17 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (32 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (47 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_44
  · change (∑ k, (if k = (6 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (15 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (13 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13

end QiushiMatmul
