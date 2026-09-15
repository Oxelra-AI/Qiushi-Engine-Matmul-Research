import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0494Refs : Fin 43 → RowRef 1665 43 := ![.occ 119, .occ 121, .occ 132, .occ 135, .occ 136, .occ 137, .occ 138, .occ 142, .occ 329, .occ 441, .occ 532, .occ 610, .occ 623, .occ 978, .occ 984, .occ 1240, .occ 1246, .occ 1343, .occ 1373, .occ 1374, .occ 1395, .occ 1401, .occ 1402, .occ 1405, .occ 1483, .occ 1507, .occ 1535, .occ 1590, .occ 1622, .occ 1628, .occ 1659, .sumGe, .nonneg 0, .nonneg 1, .nonneg 3, .branchGe 15 (1), .branchLe 35 (0), .branchGe 7 (1), .branchLe 32 (0), .branchLe 14 (0), .branchLe 36 (0), .branchLe 10 (0), .branchGe 11 (1)]

def plane484GenLeaf0494Mult : Fin 43 → Nat := ![11232, 4926, 74, 2177, 609, 1308, 7598, 1156, 794, 6607, 564, 3834, 1309, 797, 175, 46, 621, 3778, 111, 1247, 32, 3808, 4636, 1026, 207, 1172, 959, 5934, 46, 625, 207, 11899, 816, 380, 4884, 24596, 11692, 26607, 11899, 8858, 11899, 3248, 19863]

theorem plane484GenLeaf0494 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0494Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0494Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0494Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0494Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 132
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 142
  · exact hroot.hOcc 329
  · exact hroot.hOcc 441
  · exact hroot.hOcc 532
  · exact hroot.hOcc 610
  · exact hroot.hOcc 623
  · exact hroot.hOcc 978
  · exact hroot.hOcc 984
  · exact hroot.hOcc 1240
  · exact hroot.hOcc 1246
  · exact hroot.hOcc 1343
  · exact hroot.hOcc 1373
  · exact hroot.hOcc 1374
  · exact hroot.hOcc 1395
  · exact hroot.hOcc 1401
  · exact hroot.hOcc 1402
  · exact hroot.hOcc 1405
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1507
  · exact hroot.hOcc 1535
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1622
  · exact hroot.hOcc 1628
  · exact hroot.hOcc 1659
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11

end QiushiMatmul
