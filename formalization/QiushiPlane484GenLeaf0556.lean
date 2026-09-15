import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0556Refs : Fin 42 → RowRef 1665 43 := ![.occ 120, .occ 124, .occ 126, .occ 131, .occ 137, .occ 138, .occ 139, .occ 140, .occ 142, .occ 217, .occ 220, .occ 387, .occ 452, .occ 515, .occ 645, .occ 652, .occ 924, .occ 1183, .occ 1208, .occ 1266, .occ 1297, .occ 1334, .occ 1344, .occ 1345, .occ 1513, .occ 1534, .occ 1555, .occ 1573, .occ 1619, .occ 1650, .sumGe, .nonneg 2, .nonneg 14, .nonneg 22, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchGe 26 (1), .branchLe 17 (0), .branchLe 42 (0), .branchLe 12 (0), .branchGe 10 (1)]

def plane484GenLeaf0556Mult : Fin 42 → Nat := ![408, 96, 348, 100, 87, 629, 143, 645, 424, 896, 168, 618, 130, 518, 148, 116, 76, 74, 108, 140, 586, 108, 164, 16, 32, 26, 584, 90, 8, 44, 940, 384, 32, 2448, 2556, 2230, 516, 5106, 208, 940, 328, 2004]

theorem plane484GenLeaf0556 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0556Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0556Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0556Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0556Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 124
  · exact hroot.hOcc 126
  · exact hroot.hOcc 131
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 142
  · exact hroot.hOcc 217
  · exact hroot.hOcc 220
  · exact hroot.hOcc 387
  · exact hroot.hOcc 452
  · exact hroot.hOcc 515
  · exact hroot.hOcc 645
  · exact hroot.hOcc 652
  · exact hroot.hOcc 924
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1266
  · exact hroot.hOcc 1297
  · exact hroot.hOcc 1334
  · exact hroot.hOcc 1344
  · exact hroot.hOcc 1345
  · exact hroot.hOcc 1513
  · exact hroot.hOcc 1534
  · exact hroot.hOcc 1555
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1619
  · exact hroot.hOcc 1650
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (12 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
