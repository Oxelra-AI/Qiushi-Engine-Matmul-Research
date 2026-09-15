import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0051Refs : Fin 39 → RowRef 1665 43 := ![.occ 132, .occ 139, .occ 141, .occ 484, .occ 489, .occ 520, .occ 533, .occ 540, .occ 609, .occ 1006, .occ 1208, .occ 1234, .occ 1305, .occ 1308, .occ 1320, .occ 1336, .occ 1392, .occ 1398, .occ 1399, .occ 1429, .occ 1470, .occ 1518, .occ 1522, .occ 1524, .occ 1599, .occ 1610, .occ 1626, .occ 1655, .sumGe, .nonneg 0, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchGe 17 (1), .branchLe 7 (0), .branchGe 18 (1), .branchGe 41 (1)]

def plane484GenLeaf0051Mult : Fin 39 → Nat := ![1355, 1456, 2205, 2178, 280, 1956, 2578, 1830, 1026, 224, 730, 506, 223, 914, 822, 1309, 129, 597, 745, 460, 963, 140, 132, 457, 110, 2306, 114, 1941, 5200, 780, 5200, 5200, 5200, 5200, 4378, 3168, 4470, 20098, 13092]

theorem plane484GenLeaf0051 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_41 : (1 : Int) ≤ x 41)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0051Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0051Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0051Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0051Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 132
  · exact hroot.hOcc 139
  · exact hroot.hOcc 141
  · exact hroot.hOcc 484
  · exact hroot.hOcc 489
  · exact hroot.hOcc 520
  · exact hroot.hOcc 533
  · exact hroot.hOcc 540
  · exact hroot.hOcc 609
  · exact hroot.hOcc 1006
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1234
  · exact hroot.hOcc 1305
  · exact hroot.hOcc 1308
  · exact hroot.hOcc 1320
  · exact hroot.hOcc 1336
  · exact hroot.hOcc 1392
  · exact hroot.hOcc 1398
  · exact hroot.hOcc 1399
  · exact hroot.hOcc 1429
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1518
  · exact hroot.hOcc 1522
  · exact hroot.hOcc 1524
  · exact hroot.hOcc 1599
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1626
  · exact hroot.hOcc 1655
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (41 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_41

end QiushiMatmul
