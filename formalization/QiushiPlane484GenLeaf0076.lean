import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0076Refs : Fin 40 → RowRef 1665 43 := ![.occ 121, .occ 124, .occ 129, .occ 139, .occ 183, .occ 545, .occ 778, .occ 779, .occ 780, .occ 1028, .occ 1031, .occ 1191, .occ 1226, .occ 1346, .occ 1375, .occ 1376, .occ 1379, .occ 1403, .occ 1422, .occ 1458, .occ 1531, .occ 1532, .occ 1533, .occ 1559, .occ 1608, .occ 1624, .occ 1628, .occ 1634, .occ 1635, .occ 1663, .sumGe, .nonneg 5, .branchLe 15 (0), .branchLe 29 (0), .branchLe 4 (0), .branchGe 13 (1), .branchGe 42 (1), .branchLe 9 (0), .branchLe 20 (0), .branchGe 7 (1)]

def plane484GenLeaf0076Mult : Fin 40 → Nat := ![654, 844, 720, 50, 40, 296, 142, 82, 426, 90, 61, 44, 44, 163, 45, 426, 79, 22, 22, 316, 351, 118, 211, 272, 22, 300, 36, 14, 154, 14, 1056, 3196, 1056, 1056, 44, 4208, 744, 50, 1042, 3896]

theorem plane484GenLeaf0076 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0076Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0076Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0076Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0076Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 124
  · exact hroot.hOcc 129
  · exact hroot.hOcc 139
  · exact hroot.hOcc 183
  · exact hroot.hOcc 545
  · exact hroot.hOcc 778
  · exact hroot.hOcc 779
  · exact hroot.hOcc 780
  · exact hroot.hOcc 1028
  · exact hroot.hOcc 1031
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1226
  · exact hroot.hOcc 1346
  · exact hroot.hOcc 1375
  · exact hroot.hOcc 1376
  · exact hroot.hOcc 1379
  · exact hroot.hOcc 1403
  · exact hroot.hOcc 1422
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1531
  · exact hroot.hOcc 1532
  · exact hroot.hOcc 1533
  · exact hroot.hOcc 1559
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1624
  · exact hroot.hOcc 1628
  · exact hroot.hOcc 1634
  · exact hroot.hOcc 1635
  · exact hroot.hOcc 1663
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (9 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7

end QiushiMatmul
