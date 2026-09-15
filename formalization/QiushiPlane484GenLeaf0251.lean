import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0251Refs : Fin 44 → RowRef 1665 43 := ![.occ 125, .occ 126, .occ 134, .occ 136, .occ 137, .occ 139, .occ 623, .occ 699, .occ 749, .occ 858, .occ 1143, .occ 1145, .occ 1158, .occ 1173, .occ 1190, .occ 1191, .occ 1208, .occ 1213, .occ 1220, .occ 1244, .occ 1358, .occ 1387, .occ 1457, .occ 1478, .occ 1481, .occ 1489, .occ 1493, .occ 1495, .occ 1567, .occ 1610, .occ 1634, .sumGe, .nonneg 17, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchLe 29 (0), .branchGe 16 (1), .branchLe 13 (0), .branchGe 41 (1), .branchGe 40 (1), .branchLe 10 (0)]

def plane484GenLeaf0251Mult : Fin 44 → Nat := ![6026, 514, 3769, 6297, 2233, 6597, 210, 2024, 348, 368, 746, 232, 5478, 720, 3628, 4474, 1252, 420, 1346, 592, 5598, 660, 1156, 1046, 1238, 2590, 260, 4372, 2842, 1098, 1472, 14240, 9042, 2796, 23052, 11002, 5190, 3938, 10160, 35628, 1046, 12716, 9260, 12254]

theorem plane484GenLeaf0251 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_40 : (1 : Int) ≤ x 40)
    (hLB_41 : (1 : Int) ≤ x 41)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0251Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0251Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0251Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0251Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 125
  · exact hroot.hOcc 126
  · exact hroot.hOcc 134
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 139
  · exact hroot.hOcc 623
  · exact hroot.hOcc 699
  · exact hroot.hOcc 749
  · exact hroot.hOcc 858
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1244
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1387
  · exact hroot.hOcc 1457
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1493
  · exact hroot.hOcc 1495
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1634
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (41 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_41
  · change (∑ k, (if k = (40 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_40
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10

end QiushiMatmul
