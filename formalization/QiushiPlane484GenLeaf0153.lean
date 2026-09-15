import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0153Refs : Fin 43 → RowRef 1665 43 := ![.occ 93, .occ 119, .occ 121, .occ 124, .occ 129, .occ 134, .occ 179, .occ 328, .occ 368, .occ 481, .occ 560, .occ 1164, .occ 1166, .occ 1235, .occ 1238, .occ 1257, .occ 1272, .occ 1309, .occ 1337, .occ 1352, .occ 1532, .occ 1538, .occ 1548, .occ 1549, .occ 1554, .occ 1571, .occ 1590, .occ 1621, .occ 1625, .occ 1647, .occ 1649, .occ 1655, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchGe 7 (1), .branchLe 18 (0), .branchLe 30 (0), .branchLe 21 (0), .branchLe 42 (0), .branchLe 26 (0)]

def plane484GenLeaf0153Mult : Fin 43 → Nat := ![5716, 5688, 13332, 1284, 3936, 5076, 9244, 502, 5774, 2758, 5878, 7212, 9776, 100, 6138, 496, 936, 2840, 2538, 2538, 4401, 3788, 2290, 3609, 3116, 4027, 3864, 4904, 2334, 8249, 1709, 625, 33850, 24982, 20290, 12602, 28114, 55636, 24106, 27514, 33850, 33850, 22840]

theorem plane484GenLeaf0153 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0153Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0153Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0153Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0153Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 93
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 124
  · exact hroot.hOcc 129
  · exact hroot.hOcc 134
  · exact hroot.hOcc 179
  · exact hroot.hOcc 328
  · exact hroot.hOcc 368
  · exact hroot.hOcc 481
  · exact hroot.hOcc 560
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1235
  · exact hroot.hOcc 1238
  · exact hroot.hOcc 1257
  · exact hroot.hOcc 1272
  · exact hroot.hOcc 1309
  · exact hroot.hOcc 1337
  · exact hroot.hOcc 1352
  · exact hroot.hOcc 1532
  · exact hroot.hOcc 1538
  · exact hroot.hOcc 1548
  · exact hroot.hOcc 1549
  · exact hroot.hOcc 1554
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1621
  · exact hroot.hOcc 1625
  · exact hroot.hOcc 1647
  · exact hroot.hOcc 1649
  · exact hroot.hOcc 1655
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (21 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26

end QiushiMatmul
