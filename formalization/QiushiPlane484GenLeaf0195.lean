import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0195Refs : Fin 44 → RowRef 1665 43 := ![.occ 124, .occ 129, .occ 133, .occ 138, .occ 142, .occ 201, .occ 216, .occ 220, .occ 290, .occ 309, .occ 437, .occ 789, .occ 810, .occ 849, .occ 879, .occ 897, .occ 1025, .occ 1127, .occ 1140, .occ 1151, .occ 1154, .occ 1173, .occ 1259, .occ 1269, .occ 1299, .occ 1353, .occ 1427, .occ 1440, .occ 1445, .occ 1486, .occ 1505, .occ 1571, .occ 1597, .sumGe, .nonneg 1, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchGe 35 (1), .branchLe 16 (0), .branchGe 5 (1), .branchGe 22 (1), .branchGe 19 (1), .branchLe 24 (0)]

def plane484GenLeaf0195Mult : Fin 44 → Nat := ![129, 296, 425, 327, 14, 621, 96, 38, 425, 44, 552, 421, 753, 1020, 50, 355, 1149, 658, 800, 477, 316, 425, 772, 380, 131, 52, 279, 117, 263, 37, 14, 373, 425, 1870, 573, 987, 1004, 6125, 2747, 1856, 5897, 1519, 5120, 1870]

theorem plane484GenLeaf0195 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0195Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0195Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0195Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0195Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 124
  · exact hroot.hOcc 129
  · exact hroot.hOcc 133
  · exact hroot.hOcc 138
  · exact hroot.hOcc 142
  · exact hroot.hOcc 201
  · exact hroot.hOcc 216
  · exact hroot.hOcc 220
  · exact hroot.hOcc 290
  · exact hroot.hOcc 309
  · exact hroot.hOcc 437
  · exact hroot.hOcc 789
  · exact hroot.hOcc 810
  · exact hroot.hOcc 849
  · exact hroot.hOcc 879
  · exact hroot.hOcc 897
  · exact hroot.hOcc 1025
  · exact hroot.hOcc 1127
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1259
  · exact hroot.hOcc 1269
  · exact hroot.hOcc 1299
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1427
  · exact hroot.hOcc 1440
  · exact hroot.hOcc 1445
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1505
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1597
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24

end QiushiMatmul
