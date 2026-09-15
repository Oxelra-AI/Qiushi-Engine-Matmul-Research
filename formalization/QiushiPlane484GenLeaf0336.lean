import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0336Refs : Fin 42 → RowRef 1665 43 := ![.occ 122, .occ 124, .occ 137, .occ 140, .occ 141, .occ 176, .occ 184, .occ 452, .occ 757, .occ 871, .occ 1101, .occ 1146, .occ 1147, .occ 1205, .occ 1214, .occ 1428, .occ 1443, .occ 1481, .occ 1496, .occ 1506, .occ 1517, .occ 1547, .occ 1558, .occ 1573, .occ 1590, .occ 1609, .occ 1610, .sumGe, .nonneg 15, .nonneg 16, .nonneg 20, .nonneg 23, .nonneg 24, .branchGe 2 (1), .branchLe 7 (0), .branchGe 26 (1), .branchLe 14 (0), .branchGe 1 (1), .branchGe 30 (1), .branchLe 36 (0), .branchGe 27 (1), .branchGe 17 (1)]

def plane484GenLeaf0336Mult : Fin 42 → Nat := ![812, 186, 2379, 2379, 2221, 608, 227, 253, 756, 489, 315, 621, 630, 1128, 84, 439, 588, 216, 222, 158, 463, 25, 374, 546, 580, 109, 49, 2379, 1708, 216, 6489, 2019, 84, 2421, 685, 9601, 2163, 2919, 1569, 1611, 3249, 10053]

theorem plane484GenLeaf0336 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0336Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0336Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0336Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0336Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 122
  · exact hroot.hOcc 124
  · exact hroot.hOcc 137
  · exact hroot.hOcc 140
  · exact hroot.hOcc 141
  · exact hroot.hOcc 176
  · exact hroot.hOcc 184
  · exact hroot.hOcc 452
  · exact hroot.hOcc 757
  · exact hroot.hOcc 871
  · exact hroot.hOcc 1101
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1428
  · exact hroot.hOcc 1443
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1506
  · exact hroot.hOcc 1517
  · exact hroot.hOcc 1547
  · exact hroot.hOcc 1558
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1610
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (27 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17

end QiushiMatmul
