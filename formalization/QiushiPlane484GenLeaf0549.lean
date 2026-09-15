import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0549Refs : Fin 37 → RowRef 1665 43 := ![.occ 123, .occ 130, .occ 131, .occ 133, .occ 138, .occ 142, .occ 295, .occ 591, .occ 640, .occ 858, .occ 1101, .occ 1154, .occ 1206, .occ 1208, .occ 1467, .occ 1472, .occ 1570, .occ 1590, .occ 1597, .occ 1606, .occ 1637, .occ 1654, .sumGe, .nonneg 3, .nonneg 7, .nonneg 17, .nonneg 24, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchLe 26 (0), .branchGe 30 (1), .branchGe 1 (1), .branchLe 11 (0), .branchLe 32 (0), .branchGe 28 (1), .branchGe 9 (1)]

def plane484GenLeaf0549Mult : Fin 37 → Nat := ![6, 4, 1, 2, 1, 1, 4, 4, 2, 1, 2, 2, 2, 6, 2, 2, 2, 2, 4, 6, 2, 6, 12, 8, 6, 2, 4, 16, 22, 6, 2, 12, 18, 8, 6, 20, 32]

theorem plane484GenLeaf0549 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0549Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0549Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0549Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0549Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 123
  · exact hroot.hOcc 130
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 138
  · exact hroot.hOcc 142
  · exact hroot.hOcc 295
  · exact hroot.hOcc 591
  · exact hroot.hOcc 640
  · exact hroot.hOcc 858
  · exact hroot.hOcc 1101
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1570
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1637
  · exact hroot.hOcc 1654
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (11 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (9 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9

end QiushiMatmul
