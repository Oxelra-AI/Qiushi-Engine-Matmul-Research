import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0545Refs : Fin 44 → RowRef 1665 43 := ![.occ 121, .occ 129, .occ 130, .occ 133, .occ 140, .occ 196, .occ 224, .occ 277, .occ 295, .occ 326, .occ 330, .occ 377, .occ 674, .occ 735, .occ 861, .occ 948, .occ 1158, .occ 1173, .occ 1179, .occ 1188, .occ 1190, .occ 1200, .occ 1300, .occ 1344, .occ 1458, .occ 1467, .occ 1477, .occ 1483, .occ 1484, .occ 1566, .occ 1619, .occ 1650, .sumGe, .nonneg 11, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchLe 26 (0), .branchGe 30 (1), .branchGe 1 (1), .branchLe 32 (0), .branchLe 28 (0), .branchLe 8 (0), .branchGe 13 (1)]

def plane484GenLeaf0545Mult : Fin 44 → Nat := ![404, 138, 69, 173, 206, 43, 163, 166, 316, 8, 147, 29, 127, 153, 121, 28, 43, 119, 95, 35, 199, 60, 36, 36, 4, 43, 163, 86, 172, 69, 105, 127, 621, 130, 1179, 753, 349, 183, 929, 715, 330, 535, 235, 1385]

theorem plane484GenLeaf0545 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0545Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0545Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0545Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0545Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 129
  · exact hroot.hOcc 130
  · exact hroot.hOcc 133
  · exact hroot.hOcc 140
  · exact hroot.hOcc 196
  · exact hroot.hOcc 224
  · exact hroot.hOcc 277
  · exact hroot.hOcc 295
  · exact hroot.hOcc 326
  · exact hroot.hOcc 330
  · exact hroot.hOcc 377
  · exact hroot.hOcc 674
  · exact hroot.hOcc 735
  · exact hroot.hOcc 861
  · exact hroot.hOcc 948
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1300
  · exact hroot.hOcc 1344
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1566
  · exact hroot.hOcc 1619
  · exact hroot.hOcc 1650
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13

end QiushiMatmul
