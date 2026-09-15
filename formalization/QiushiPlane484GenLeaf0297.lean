import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0297Refs : Fin 44 → RowRef 1665 43 := ![.occ 84, .occ 85, .occ 121, .occ 122, .occ 141, .occ 187, .occ 192, .occ 614, .occ 1109, .occ 1113, .occ 1140, .occ 1151, .occ 1160, .occ 1170, .occ 1180, .occ 1200, .occ 1258, .occ 1459, .occ 1488, .occ 1489, .occ 1492, .occ 1526, .occ 1567, .occ 1571, .occ 1609, .occ 1622, .occ 1641, .occ 1649, .occ 1650, .occ 1656, .sumGe, .nonneg 4, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchGe 29 (1), .branchGe 34 (1), .branchLe 36 (0), .branchLe 22 (0), .branchGe 32 (1), .branchLe 28 (0), .branchLe 12 (0)]

def plane484GenLeaf0297Mult : Fin 44 → Nat := ![132398, 79422, 39699, 113526, 139246, 147420, 36344, 74042, 47110, 210385, 122075, 117831, 65595, 29835, 33490, 44377, 36429, 68169, 216823, 74135, 224535, 82925, 271289, 77217, 151910, 6203, 139594, 13864, 107703, 73283, 735572, 80036, 545398, 467040, 436430, 653539, 409137, 929345, 490377, 735572, 372252, 1099403, 450419, 492860]

theorem plane484GenLeaf0297 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0297Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0297Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0297Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0297Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 84
  · exact hroot.hOcc 85
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 141
  · exact hroot.hOcc 187
  · exact hroot.hOcc 192
  · exact hroot.hOcc 614
  · exact hroot.hOcc 1109
  · exact hroot.hOcc 1113
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1180
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1258
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1526
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1622
  · exact hroot.hOcc 1641
  · exact hroot.hOcc 1649
  · exact hroot.hOcc 1650
  · exact hroot.hOcc 1656
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (32 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (12 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12

end QiushiMatmul
