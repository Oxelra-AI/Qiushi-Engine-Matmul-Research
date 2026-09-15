import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0259Refs : Fin 44 → RowRef 1665 43 := ![.occ 105, .occ 125, .occ 135, .occ 137, .occ 140, .occ 141, .occ 150, .occ 585, .occ 661, .occ 974, .occ 976, .occ 1143, .occ 1170, .occ 1186, .occ 1190, .occ 1191, .occ 1196, .occ 1205, .occ 1254, .occ 1275, .occ 1333, .occ 1368, .occ 1382, .occ 1435, .occ 1478, .occ 1483, .occ 1489, .occ 1502, .occ 1506, .occ 1537, .occ 1602, .occ 1609, .sumGe, .nonneg 15, .nonneg 16, .nonneg 19, .nonneg 26, .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 29 (0), .branchGe 17 (1), .branchLe 3 (0), .branchGe 20 (1)]

def plane484GenLeaf0259Mult : Fin 44 → Nat := ![7748, 25082, 4426, 33549, 36832, 31250, 3402, 17035, 5546, 1875, 399, 365, 5458, 739, 17696, 2824, 3309, 739, 7017, 3415, 898, 2268, 12849, 1412, 8365, 7162, 4652, 12729, 8483, 3695, 6130, 3098, 45936, 7536, 8133, 7536, 96527, 53868, 42627, 12387, 45936, 134181, 45936, 155761]

theorem plane484GenLeaf0259 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0259Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0259Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0259Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0259Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 105
  · exact hroot.hOcc 125
  · exact hroot.hOcc 135
  · exact hroot.hOcc 137
  · exact hroot.hOcc 140
  · exact hroot.hOcc 141
  · exact hroot.hOcc 150
  · exact hroot.hOcc 585
  · exact hroot.hOcc 661
  · exact hroot.hOcc 974
  · exact hroot.hOcc 976
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1254
  · exact hroot.hOcc 1275
  · exact hroot.hOcc 1333
  · exact hroot.hOcc 1368
  · exact hroot.hOcc 1382
  · exact hroot.hOcc 1435
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1502
  · exact hroot.hOcc 1506
  · exact hroot.hOcc 1537
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1609
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20

end QiushiMatmul
