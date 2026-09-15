import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0390Refs : Fin 41 → RowRef 1665 43 := ![.occ 120, .occ 125, .occ 126, .occ 128, .occ 130, .occ 131, .occ 137, .occ 138, .occ 319, .occ 587, .occ 589, .occ 590, .occ 641, .occ 709, .occ 710, .occ 712, .occ 773, .occ 1038, .occ 1187, .occ 1196, .occ 1206, .occ 1213, .occ 1438, .occ 1442, .occ 1458, .occ 1481, .occ 1484, .occ 1486, .occ 1492, .occ 1496, .occ 1606, .sumGe, .nonneg 15, .branchGe 2 (1), .branchLe 7 (0), .branchGe 23 (1), .branchGe 35 (1), .branchGe 30 (1), .branchGe 42 (1), .branchGe 39 (1), .branchGe 10 (1)]

def plane484GenLeaf0390Mult : Fin 41 → Nat := ![39, 24, 38, 35, 4, 32, 50, 48, 2, 14, 29, 67, 120, 29, 45, 10, 17, 7, 8, 3, 53, 16, 42, 28, 16, 3, 30, 22, 43, 22, 45, 120, 43, 171, 57, 354, 198, 182, 239, 172, 443]

theorem plane484GenLeaf0390 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0390Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0390Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0390Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0390Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 125
  · exact hroot.hOcc 126
  · exact hroot.hOcc 128
  · exact hroot.hOcc 130
  · exact hroot.hOcc 131
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 319
  · exact hroot.hOcc 587
  · exact hroot.hOcc 589
  · exact hroot.hOcc 590
  · exact hroot.hOcc 641
  · exact hroot.hOcc 709
  · exact hroot.hOcc 710
  · exact hroot.hOcc 712
  · exact hroot.hOcc 773
  · exact hroot.hOcc 1038
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1438
  · exact hroot.hOcc 1442
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1606
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (39 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
