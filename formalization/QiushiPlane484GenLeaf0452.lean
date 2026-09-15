import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0452Refs : Fin 44 → RowRef 1665 43 := ![.occ 97, .occ 124, .occ 134, .occ 138, .occ 146, .occ 163, .occ 191, .occ 328, .occ 329, .occ 581, .occ 654, .occ 872, .occ 997, .occ 1070, .occ 1072, .occ 1082, .occ 1140, .occ 1262, .occ 1265, .occ 1269, .occ 1276, .occ 1310, .occ 1343, .occ 1503, .occ 1555, .occ 1567, .occ 1640, .occ 1645, .occ 1646, .occ 1649, .occ 1652, .occ 1656, .sumGe, .nonneg 11, .nonneg 19, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 0 (0), .branchGe 29 (1), .branchLe 27 (0), .branchLe 42 (0), .branchLe 40 (0), .branchGe 28 (1)]

def plane484GenLeaf0452Mult : Fin 44 → Nat := ![1261, 874, 74, 2591, 1513, 725, 1207, 470, 3390, 1357, 6404, 1960, 1439, 63, 1025, 699, 996, 830, 845, 1668, 3150, 2679, 1910, 202, 126, 5448, 609, 1910, 2468, 1838, 2037, 4208, 13900, 505, 2462, 21192, 10482, 11116, 13900, 20353, 11990, 13900, 13900, 12681]

theorem plane484GenLeaf0452 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0452Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0452Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0452Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0452Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 97
  · exact hroot.hOcc 124
  · exact hroot.hOcc 134
  · exact hroot.hOcc 138
  · exact hroot.hOcc 146
  · exact hroot.hOcc 163
  · exact hroot.hOcc 191
  · exact hroot.hOcc 328
  · exact hroot.hOcc 329
  · exact hroot.hOcc 581
  · exact hroot.hOcc 654
  · exact hroot.hOcc 872
  · exact hroot.hOcc 997
  · exact hroot.hOcc 1070
  · exact hroot.hOcc 1072
  · exact hroot.hOcc 1082
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1262
  · exact hroot.hOcc 1265
  · exact hroot.hOcc 1269
  · exact hroot.hOcc 1276
  · exact hroot.hOcc 1310
  · exact hroot.hOcc 1343
  · exact hroot.hOcc 1503
  · exact hroot.hOcc 1555
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1640
  · exact hroot.hOcc 1645
  · exact hroot.hOcc 1646
  · exact hroot.hOcc 1649
  · exact hroot.hOcc 1652
  · exact hroot.hOcc 1656
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (27 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (40 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28

end QiushiMatmul
