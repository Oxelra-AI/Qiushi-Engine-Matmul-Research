import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0360Refs : Fin 44 → RowRef 1665 43 := ![.occ 123, .occ 125, .occ 135, .occ 138, .occ 141, .occ 167, .occ 559, .occ 606, .occ 860, .occ 1078, .occ 1146, .occ 1188, .occ 1190, .occ 1200, .occ 1216, .occ 1224, .occ 1256, .occ 1295, .occ 1305, .occ 1383, .occ 1389, .occ 1399, .occ 1438, .occ 1459, .occ 1491, .occ 1496, .occ 1567, .occ 1610, .occ 1625, .occ 1655, .sumGe, .nonneg 1, .nonneg 15, .nonneg 20, .nonneg 22, .nonneg 26, .branchGe 2 (1), .branchLe 7 (0), .branchGe 23 (1), .branchLe 35 (0), .branchLe 3 (0), .branchLe 24 (0), .branchGe 18 (1), .branchGe 25 (1)]

def plane484GenLeaf0360Mult : Fin 44 → Nat := ![17605, 12763, 42442, 19850, 25878, 4816, 4878, 4386, 33694, 1376, 9692, 3820, 1756, 13174, 11018, 3359, 15413, 2100, 950, 5693, 4342, 3523, 3106, 7528, 1734, 12026, 4920, 8832, 1056, 6414, 46784, 852, 32502, 62700, 48694, 32736, 92998, 44684, 82282, 34758, 7030, 2608, 148712, 92244]

theorem plane484GenLeaf0360 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0360Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0360Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0360Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0360Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 123
  · exact hroot.hOcc 125
  · exact hroot.hOcc 135
  · exact hroot.hOcc 138
  · exact hroot.hOcc 141
  · exact hroot.hOcc 167
  · exact hroot.hOcc 559
  · exact hroot.hOcc 606
  · exact hroot.hOcc 860
  · exact hroot.hOcc 1078
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1224
  · exact hroot.hOcc 1256
  · exact hroot.hOcc 1295
  · exact hroot.hOcc 1305
  · exact hroot.hOcc 1383
  · exact hroot.hOcc 1389
  · exact hroot.hOcc 1399
  · exact hroot.hOcc 1438
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1625
  · exact hroot.hOcc 1655
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25

end QiushiMatmul
