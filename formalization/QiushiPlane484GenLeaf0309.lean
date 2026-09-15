import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0309Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 122, .occ 131, .occ 180, .occ 185, .occ 200, .occ 204, .occ 206, .occ 216, .occ 218, .occ 222, .occ 350, .occ 614, .occ 858, .occ 1101, .occ 1136, .occ 1140, .occ 1143, .occ 1154, .occ 1183, .occ 1191, .occ 1196, .occ 1216, .occ 1327, .occ 1477, .occ 1488, .occ 1491, .occ 1597, .occ 1601, .occ 1623, .occ 1649, .sumGe, .nonneg 42, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchGe 29 (1), .branchGe 34 (1), .branchGe 36 (1), .branchGe 30 (1), .branchLe 12 (0), .branchGe 20 (1)]

def plane484GenLeaf0309Mult : Fin 44 → Nat := ![1705, 3940, 3959, 2890, 6490, 1926, 723, 451, 781, 14378, 202, 11211, 8405, 2147, 4185, 7897, 3904, 3021, 5439, 8540, 7048, 1520, 3707, 4624, 6288, 13644, 3975, 280, 6082, 2781, 2095, 26131, 3858, 20025, 25059, 9105, 20077, 19643, 49678, 39537, 50878, 27743, 17378, 46150]

theorem plane484GenLeaf0309 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0309Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0309Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0309Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0309Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 122
  · exact hroot.hOcc 131
  · exact hroot.hOcc 180
  · exact hroot.hOcc 185
  · exact hroot.hOcc 200
  · exact hroot.hOcc 204
  · exact hroot.hOcc 206
  · exact hroot.hOcc 216
  · exact hroot.hOcc 218
  · exact hroot.hOcc 222
  · exact hroot.hOcc 350
  · exact hroot.hOcc 614
  · exact hroot.hOcc 858
  · exact hroot.hOcc 1101
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1327
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1623
  · exact hroot.hOcc 1649
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (36 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (12 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20

end QiushiMatmul
