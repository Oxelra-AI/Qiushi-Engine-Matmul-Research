import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0345Refs : Fin 43 → RowRef 1665 43 := ![.occ 124, .occ 125, .occ 128, .occ 129, .occ 137, .occ 138, .occ 139, .occ 142, .occ 364, .occ 387, .occ 631, .occ 706, .occ 818, .occ 848, .occ 974, .occ 1143, .occ 1172, .occ 1213, .occ 1233, .occ 1382, .occ 1384, .occ 1481, .occ 1492, .occ 1513, .occ 1522, .occ 1525, .occ 1573, .occ 1622, .sumGe, .nonneg 3, .nonneg 4, .nonneg 8, .nonneg 11, .nonneg 17, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchGe 26 (1), .branchGe 14 (1), .branchLe 36 (0), .branchGe 28 (1), .branchGe 5 (1)]

def plane484GenLeaf0345Mult : Fin 43 → Nat := ![29, 191, 161, 102, 73, 77, 29, 29, 14, 35, 52, 75, 38, 5, 78, 87, 52, 1, 1, 40, 43, 47, 61, 20, 41, 5, 26, 8, 191, 32, 142, 478, 47, 47, 57, 400, 32, 14, 479, 689, 165, 102, 714]

theorem plane484GenLeaf0345 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0345Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0345Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0345Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0345Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 124
  · exact hroot.hOcc 125
  · exact hroot.hOcc 128
  · exact hroot.hOcc 129
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 139
  · exact hroot.hOcc 142
  · exact hroot.hOcc 364
  · exact hroot.hOcc 387
  · exact hroot.hOcc 631
  · exact hroot.hOcc 706
  · exact hroot.hOcc 818
  · exact hroot.hOcc 848
  · exact hroot.hOcc 974
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1233
  · exact hroot.hOcc 1382
  · exact hroot.hOcc 1384
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1513
  · exact hroot.hOcc 1522
  · exact hroot.hOcc 1525
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1622
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5

end QiushiMatmul
