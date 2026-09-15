import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0411Refs : Fin 43 → RowRef 1665 43 := ![.occ 97, .occ 101, .occ 119, .occ 121, .occ 124, .occ 138, .occ 143, .occ 260, .occ 329, .occ 597, .occ 634, .occ 707, .occ 934, .occ 1134, .occ 1145, .occ 1147, .occ 1174, .occ 1196, .occ 1200, .occ 1294, .occ 1376, .occ 1444, .occ 1458, .occ 1467, .occ 1486, .occ 1489, .occ 1541, .occ 1562, .occ 1571, .occ 1607, .occ 1608, .sumGe, .nonneg 4, .branchLe 15 (0), .branchGe 2 (1), .branchGe 7 (1), .branchLe 6 (0), .branchLe 29 (0), .branchLe 14 (0), .branchLe 24 (0), .branchLe 22 (0), .branchLe 16 (0), .branchLe 41 (0)]

def plane484GenLeaf0411Mult : Fin 43 → Nat := ![589, 3346, 7490, 9831, 6922, 549, 120, 4775, 3602, 2174, 5576, 5819, 2217, 2066, 1715, 1782, 2524, 8545, 481, 1836, 1213, 2975, 1715, 2009, 80, 5317, 44, 458, 4014, 5653, 719, 19681, 1301, 10974, 11910, 48992, 17779, 13578, 19080, 17966, 9997, 17157, 19681]

theorem plane484GenLeaf0411 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_41 : x 41 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0411Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0411Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0411Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0411Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 97
  · exact hroot.hOcc 101
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 124
  · exact hroot.hOcc 138
  · exact hroot.hOcc 143
  · exact hroot.hOcc 260
  · exact hroot.hOcc 329
  · exact hroot.hOcc 597
  · exact hroot.hOcc 634
  · exact hroot.hOcc 707
  · exact hroot.hOcc 934
  · exact hroot.hOcc 1134
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1294
  · exact hroot.hOcc 1376
  · exact hroot.hOcc 1444
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1541
  · exact hroot.hOcc 1562
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1608
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (41 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_41

end QiushiMatmul
