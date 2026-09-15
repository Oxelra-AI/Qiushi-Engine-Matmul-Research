import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0181Refs : Fin 42 → RowRef 1665 43 := ![.occ 130, .occ 198, .occ 199, .occ 550, .occ 582, .occ 647, .occ 692, .occ 1151, .occ 1160, .occ 1173, .occ 1220, .occ 1241, .occ 1290, .occ 1328, .occ 1357, .occ 1440, .occ 1453, .occ 1478, .occ 1492, .occ 1496, .occ 1505, .occ 1538, .occ 1543, .occ 1548, .occ 1561, .occ 1606, .occ 1607, .occ 1623, .occ 1662, .sumGe, .nonneg 15, .branchLe 2 (0), .branchGe 29 (1), .branchGe 35 (1), .branchLe 16 (0), .branchLe 18 (0), .branchLe 1 (0), .branchLe 5 (0), .branchLe 7 (0), .branchLe 14 (0), .branchGe 4 (1), .branchGe 33 (1)]

def plane484GenLeaf0181Mult : Fin 42 → Nat := ![6451, 1695, 15166, 12508, 4065, 4778, 2940, 1696, 2798, 2886, 3914, 13774, 981, 827, 3552, 7177, 2530, 1004, 6587, 4134, 12306, 4302, 2225, 5998, 2033, 338, 877, 1831, 1604, 24251, 834, 13530, 53557, 75538, 13597, 19622, 21551, 18286, 15545, 11479, 50224, 45023]

theorem plane484GenLeaf0181 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_33 : (1 : Int) ≤ x 33)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0181Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0181Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0181Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0181Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 130
  · exact hroot.hOcc 198
  · exact hroot.hOcc 199
  · exact hroot.hOcc 550
  · exact hroot.hOcc 582
  · exact hroot.hOcc 647
  · exact hroot.hOcc 692
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1241
  · exact hroot.hOcc 1290
  · exact hroot.hOcc 1328
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1440
  · exact hroot.hOcc 1453
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1505
  · exact hroot.hOcc 1538
  · exact hroot.hOcc 1543
  · exact hroot.hOcc 1548
  · exact hroot.hOcc 1561
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1623
  · exact hroot.hOcc 1662
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (33 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_33

end QiushiMatmul
