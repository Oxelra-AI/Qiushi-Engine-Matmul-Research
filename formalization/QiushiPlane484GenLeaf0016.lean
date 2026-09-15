import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0016Refs : Fin 44 → RowRef 1665 43 := ![.occ 121, .occ 127, .occ 134, .occ 145, .occ 441, .occ 444, .occ 445, .occ 508, .occ 1039, .occ 1166, .occ 1168, .occ 1174, .occ 1183, .occ 1282, .occ 1336, .occ 1396, .occ 1406, .occ 1407, .occ 1408, .occ 1410, .occ 1422, .occ 1434, .occ 1462, .occ 1474, .occ 1508, .occ 1608, .occ 1626, .occ 1630, .occ 1655, .occ 1659, .occ 1664, .sumGe, .nonneg 6, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchLe 17 (0), .branchLe 35 (0), .branchGe 41 (1), .branchLe 19 (0), .branchGe 42 (1), .branchGe 7 (1)]

def plane484GenLeaf0016Mult : Fin 44 → Nat := ![13600, 172, 3678, 2010, 2126, 3028, 960, 2572, 972, 5268, 2444, 2492, 9000, 3339, 682, 2011, 2934, 3388, 7866, 795, 895, 4668, 3683, 2078, 5970, 11305, 2424, 2664, 5137, 7601, 2452, 33504, 3678, 19992, 24504, 24848, 28870, 17826, 25482, 33504, 15512, 31052, 19808, 45484]

theorem plane484GenLeaf0016 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_41 : (1 : Int) ≤ x 41)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0016Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0016Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0016Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0016Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 127
  · exact hroot.hOcc 134
  · exact hroot.hOcc 145
  · exact hroot.hOcc 441
  · exact hroot.hOcc 444
  · exact hroot.hOcc 445
  · exact hroot.hOcc 508
  · exact hroot.hOcc 1039
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1282
  · exact hroot.hOcc 1336
  · exact hroot.hOcc 1396
  · exact hroot.hOcc 1406
  · exact hroot.hOcc 1407
  · exact hroot.hOcc 1408
  · exact hroot.hOcc 1410
  · exact hroot.hOcc 1422
  · exact hroot.hOcc 1434
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1474
  · exact hroot.hOcc 1508
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1626
  · exact hroot.hOcc 1630
  · exact hroot.hOcc 1655
  · exact hroot.hOcc 1659
  · exact hroot.hOcc 1664
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (41 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_41
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7

end QiushiMatmul
