import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0234Refs : Fin 44 → RowRef 1665 43 := ![.occ 86, .occ 103, .occ 136, .occ 153, .occ 354, .occ 431, .occ 606, .occ 609, .occ 644, .occ 861, .occ 1147, .occ 1148, .occ 1156, .occ 1168, .occ 1186, .occ 1213, .occ 1214, .occ 1247, .occ 1353, .occ 1358, .occ 1441, .occ 1478, .occ 1483, .occ 1597, .occ 1606, .occ 1615, .occ 1644, .occ 1645, .occ 1647, .sumGe, .branchLe 15 (0), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchLe 29 (0), .branchLe 17 (0), .branchLe 16 (0), .branchGe 31 (1), .branchLe 20 (0), .branchLe 30 (0), .branchLe 5 (0), .branchLe 21 (0), .branchGe 28 (1), .branchLe 14 (0)]

def plane484GenLeaf0234Mult : Fin 44 → Nat := ![31, 447, 185, 466, 72, 332, 808, 959, 185, 1067, 325, 420, 230, 400, 1039, 446, 240, 31, 394, 17, 341, 211, 489, 375, 698, 1020, 300, 322, 68, 2759, 681, 2691, 1290, 1113, 2125, 2206, 178, 3973, 2226, 2759, 2384, 1018, 5382, 2245]

theorem plane484GenLeaf0234 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0234Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0234Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0234Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0234Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 86
  · exact hroot.hOcc 103
  · exact hroot.hOcc 136
  · exact hroot.hOcc 153
  · exact hroot.hOcc 354
  · exact hroot.hOcc 431
  · exact hroot.hOcc 606
  · exact hroot.hOcc 609
  · exact hroot.hOcc 644
  · exact hroot.hOcc 861
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1148
  · exact hroot.hOcc 1156
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1247
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1441
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1644
  · exact hroot.hOcc 1645
  · exact hroot.hOcc 1647
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (21 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14

end QiushiMatmul
