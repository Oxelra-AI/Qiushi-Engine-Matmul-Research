import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0111Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 130, .occ 134, .occ 200, .occ 244, .occ 281, .occ 306, .occ 354, .occ 427, .occ 697, .occ 894, .occ 901, .occ 993, .occ 998, .occ 1057, .occ 1131, .occ 1136, .occ 1150, .occ 1170, .occ 1240, .occ 1252, .occ 1264, .occ 1267, .occ 1291, .occ 1325, .occ 1437, .occ 1438, .occ 1472, .occ 1477, .occ 1497, .occ 1553, .occ 1618, .occ 1621, .occ 1631, .sumGe, .nonneg 8, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchGe 4 (1), .branchGe 36 (1), .branchLe 26 (0), .branchGe 19 (1), .branchGe 30 (1)]

def plane484GenLeaf0111Mult : Fin 44 → Nat := ![173, 221, 104, 311, 1682, 182, 46, 86, 1368, 104, 88, 142, 886, 1011, 141, 217, 245, 749, 754, 375, 106, 508, 29, 107, 305, 46, 390, 650, 429, 276, 361, 164, 449, 291, 2223, 174, 1483, 1947, 1978, 5382, 4834, 2059, 7105, 6683]

theorem plane484GenLeaf0111 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0111Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0111Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0111Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0111Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 130
  · exact hroot.hOcc 134
  · exact hroot.hOcc 200
  · exact hroot.hOcc 244
  · exact hroot.hOcc 281
  · exact hroot.hOcc 306
  · exact hroot.hOcc 354
  · exact hroot.hOcc 427
  · exact hroot.hOcc 697
  · exact hroot.hOcc 894
  · exact hroot.hOcc 901
  · exact hroot.hOcc 993
  · exact hroot.hOcc 998
  · exact hroot.hOcc 1057
  · exact hroot.hOcc 1131
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1240
  · exact hroot.hOcc 1252
  · exact hroot.hOcc 1264
  · exact hroot.hOcc 1267
  · exact hroot.hOcc 1291
  · exact hroot.hOcc 1325
  · exact hroot.hOcc 1437
  · exact hroot.hOcc 1438
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1497
  · exact hroot.hOcc 1553
  · exact hroot.hOcc 1618
  · exact hroot.hOcc 1621
  · exact hroot.hOcc 1631
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (36 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30

end QiushiMatmul
