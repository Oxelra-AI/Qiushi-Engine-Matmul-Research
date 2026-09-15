import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0377Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 120, .occ 122, .occ 123, .occ 125, .occ 126, .occ 128, .occ 130, .occ 132, .occ 137, .occ 305, .occ 311, .occ 325, .occ 330, .occ 349, .occ 550, .occ 708, .occ 860, .occ 1145, .occ 1164, .occ 1166, .occ 1170, .occ 1172, .occ 1179, .occ 1191, .occ 1263, .occ 1299, .occ 1458, .occ 1496, .occ 1571, .occ 1573, .occ 1597, .occ 1657, .sumGe, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchGe 23 (1), .branchGe 35 (1), .branchLe 30 (0), .branchLe 42 (0), .branchGe 27 (1), .branchLe 9 (0), .branchLe 28 (0)]

def plane484GenLeaf0377Mult : Fin 44 → Nat := ![85, 567, 1043, 1563, 164, 2087, 125, 246, 1807, 3069, 1192, 2182, 477, 141, 896, 2376, 34, 778, 1468, 1172, 706, 418, 118, 2118, 418, 402, 942, 42, 72, 284, 1274, 300, 888, 5294, 4676, 5582, 38, 11566, 4676, 3560, 5180, 6680, 1866, 4994]

theorem plane484GenLeaf0377 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0377Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0377Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0377Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0377Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 120
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 125
  · exact hroot.hOcc 126
  · exact hroot.hOcc 128
  · exact hroot.hOcc 130
  · exact hroot.hOcc 132
  · exact hroot.hOcc 137
  · exact hroot.hOcc 305
  · exact hroot.hOcc 311
  · exact hroot.hOcc 325
  · exact hroot.hOcc 330
  · exact hroot.hOcc 349
  · exact hroot.hOcc 550
  · exact hroot.hOcc 708
  · exact hroot.hOcc 860
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1263
  · exact hroot.hOcc 1299
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1657
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (27 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (9 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28

end QiushiMatmul
