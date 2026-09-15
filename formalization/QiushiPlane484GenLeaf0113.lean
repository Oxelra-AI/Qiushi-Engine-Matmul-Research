import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0113Refs : Fin 43 → RowRef 1665 43 := ![.occ 120, .occ 122, .occ 125, .occ 127, .occ 130, .occ 138, .occ 140, .occ 142, .occ 208, .occ 340, .occ 341, .occ 660, .occ 811, .occ 812, .occ 991, .occ 1143, .occ 1146, .occ 1238, .occ 1282, .occ 1294, .occ 1311, .occ 1316, .occ 1332, .occ 1455, .occ 1477, .occ 1524, .occ 1535, .occ 1537, .occ 1549, .occ 1573, .occ 1637, .occ 1642, .sumGe, .nonneg 2, .nonneg 15, .branchLe 29 (0), .branchGe 4 (1), .branchGe 36 (1), .branchGe 26 (1), .branchLe 21 (0), .branchLe 18 (0), .branchLe 35 (0), .branchGe 22 (1)]

def plane484GenLeaf0113Mult : Fin 43 → Nat := ![455, 484, 1094, 623, 3390, 1165, 5274, 3071, 3563, 550, 535, 3431, 1367, 3024, 2733, 821, 1068, 167, 160, 3542, 954, 954, 160, 1750, 535, 615, 615, 325, 821, 1928, 240, 1148, 6916, 548, 8284, 6516, 21174, 13276, 16479, 3845, 821, 4988, 21861]

theorem plane484GenLeaf0113 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0113Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0113Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0113Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0113Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 122
  · exact hroot.hOcc 125
  · exact hroot.hOcc 127
  · exact hroot.hOcc 130
  · exact hroot.hOcc 138
  · exact hroot.hOcc 140
  · exact hroot.hOcc 142
  · exact hroot.hOcc 208
  · exact hroot.hOcc 340
  · exact hroot.hOcc 341
  · exact hroot.hOcc 660
  · exact hroot.hOcc 811
  · exact hroot.hOcc 812
  · exact hroot.hOcc 991
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1238
  · exact hroot.hOcc 1282
  · exact hroot.hOcc 1294
  · exact hroot.hOcc 1311
  · exact hroot.hOcc 1316
  · exact hroot.hOcc 1332
  · exact hroot.hOcc 1455
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1524
  · exact hroot.hOcc 1535
  · exact hroot.hOcc 1537
  · exact hroot.hOcc 1549
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1637
  · exact hroot.hOcc 1642
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (36 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (21 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22

end QiushiMatmul
