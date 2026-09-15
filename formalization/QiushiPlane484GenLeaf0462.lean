import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0462Refs : Fin 42 → RowRef 1665 43 := ![.occ 125, .occ 130, .occ 133, .occ 138, .occ 179, .occ 191, .occ 693, .occ 813, .occ 962, .occ 1082, .occ 1102, .occ 1136, .occ 1145, .occ 1146, .occ 1147, .occ 1151, .occ 1235, .occ 1297, .occ 1317, .occ 1440, .occ 1453, .occ 1459, .occ 1467, .occ 1477, .occ 1544, .occ 1567, .occ 1590, .occ 1619, .occ 1631, .occ 1652, .occ 1653, .sumGe, .nonneg 7, .branchGe 15 (1), .branchLe 35 (0), .branchLe 0 (0), .branchGe 29 (1), .branchGe 27 (1), .branchLe 8 (0), .branchGe 4 (1), .branchLe 5 (0), .branchLe 16 (0)]

def plane484GenLeaf0462Mult : Fin 42 → Nat := ![10325, 1960, 6982, 14202, 10978, 7343, 11319, 12620, 2380, 20152, 3161, 20257, 2826, 2296, 530, 5682, 22998, 357, 788, 1719, 13908, 2373, 1496, 2343, 1930, 1602, 2479, 5950, 483, 1643, 483, 34942, 7136, 93807, 33223, 6775, 77099, 8330, 7136, 115371, 21791, 26907]

theorem plane484GenLeaf0462 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0462Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0462Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0462Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0462Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 125
  · exact hroot.hOcc 130
  · exact hroot.hOcc 133
  · exact hroot.hOcc 138
  · exact hroot.hOcc 179
  · exact hroot.hOcc 191
  · exact hroot.hOcc 693
  · exact hroot.hOcc 813
  · exact hroot.hOcc 962
  · exact hroot.hOcc 1082
  · exact hroot.hOcc 1102
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1235
  · exact hroot.hOcc 1297
  · exact hroot.hOcc 1317
  · exact hroot.hOcc 1440
  · exact hroot.hOcc 1453
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1544
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1619
  · exact hroot.hOcc 1631
  · exact hroot.hOcc 1652
  · exact hroot.hOcc 1653
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (27 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16

end QiushiMatmul
