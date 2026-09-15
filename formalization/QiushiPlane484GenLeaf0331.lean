import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0331Refs : Fin 43 → RowRef 1665 43 := ![.occ 120, .occ 121, .occ 123, .occ 125, .occ 128, .occ 137, .occ 140, .occ 578, .occ 827, .occ 848, .occ 1160, .occ 1186, .occ 1205, .occ 1208, .occ 1215, .occ 1283, .occ 1368, .occ 1382, .occ 1398, .occ 1435, .occ 1492, .occ 1547, .occ 1567, .occ 1573, .occ 1600, .occ 1607, .occ 1625, .sumGe, .nonneg 15, .nonneg 16, .nonneg 20, .nonneg 23, .nonneg 24, .branchGe 2 (1), .branchLe 7 (0), .branchGe 26 (1), .branchLe 14 (0), .branchGe 1 (1), .branchGe 30 (1), .branchLe 36 (0), .branchLe 27 (0), .branchLe 37 (0), .branchGe 17 (1)]

def plane484GenLeaf0331Mult : Fin 43 → Nat := ![35, 73, 426, 83, 115, 876, 812, 44, 84, 121, 229, 64, 113, 66, 146, 210, 14, 44, 57, 231, 33, 57, 143, 276, 466, 31, 115, 876, 49, 209, 1775, 276, 115, 1025, 649, 2433, 491, 449, 875, 586, 876, 706, 2535]

theorem plane484GenLeaf0331 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0331Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0331Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0331Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0331Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 121
  · exact hroot.hOcc 123
  · exact hroot.hOcc 125
  · exact hroot.hOcc 128
  · exact hroot.hOcc 137
  · exact hroot.hOcc 140
  · exact hroot.hOcc 578
  · exact hroot.hOcc 827
  · exact hroot.hOcc 848
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1283
  · exact hroot.hOcc 1368
  · exact hroot.hOcc 1382
  · exact hroot.hOcc 1398
  · exact hroot.hOcc 1435
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1547
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1600
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1625
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
  · change (∑ k, (if k = (27 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (37 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17

end QiushiMatmul
