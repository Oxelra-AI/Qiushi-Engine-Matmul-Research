import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0296Refs : Fin 42 → RowRef 1665 43 := ![.occ 121, .occ 123, .occ 124, .occ 125, .occ 129, .occ 136, .occ 283, .occ 290, .occ 323, .occ 329, .occ 390, .occ 858, .occ 871, .occ 1143, .occ 1154, .occ 1157, .occ 1160, .occ 1214, .occ 1269, .occ 1312, .occ 1492, .occ 1517, .occ 1597, .occ 1610, .occ 1636, .occ 1656, .sumGe, .nonneg 4, .nonneg 11, .nonneg 16, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchGe 29 (1), .branchGe 34 (1), .branchLe 36 (0), .branchLe 22 (0), .branchLe 32 (0), .branchGe 17 (1), .branchGe 5 (1)]

def plane484GenLeaf0296Mult : Fin 42 → Nat := ![43, 10, 105, 288, 137, 331, 136, 23, 153, 37, 250, 92, 140, 79, 183, 127, 32, 37, 68, 10, 22, 57, 135, 310, 297, 58, 629, 172, 27, 57, 500, 595, 47, 295, 180, 481, 396, 494, 115, 607, 923, 1557]

theorem plane484GenLeaf0296 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0296Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0296Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0296Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0296Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 125
  · exact hroot.hOcc 129
  · exact hroot.hOcc 136
  · exact hroot.hOcc 283
  · exact hroot.hOcc 290
  · exact hroot.hOcc 323
  · exact hroot.hOcc 329
  · exact hroot.hOcc 390
  · exact hroot.hOcc 858
  · exact hroot.hOcc 871
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1157
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1269
  · exact hroot.hOcc 1312
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1517
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1636
  · exact hroot.hOcc 1656
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5

end QiushiMatmul
