import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0057Refs : Fin 40 → RowRef 1665 43 := ![.occ 126, .occ 132, .occ 141, .occ 162, .occ 283, .occ 290, .occ 442, .occ 507, .occ 587, .occ 597, .occ 634, .occ 646, .occ 782, .occ 843, .occ 1205, .occ 1208, .occ 1217, .occ 1240, .occ 1313, .occ 1369, .occ 1392, .occ 1470, .occ 1506, .occ 1517, .occ 1547, .occ 1610, .occ 1626, .occ 1655, .sumGe, .nonneg 0, .nonneg 1, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchGe 17 (1), .branchGe 7 (1), .branchGe 10 (1), .branchGe 18 (1)]

def plane484GenLeaf0057Mult : Fin 40 → Nat := ![171, 179, 281, 11, 115, 23, 183, 17, 50, 57, 166, 39, 52, 2, 10, 154, 18, 46, 40, 58, 12, 172, 5, 3, 42, 44, 83, 12, 338, 290, 125, 328, 167, 338, 250, 338, 637, 570, 377, 1028]

theorem plane484GenLeaf0057 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0057Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0057Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0057Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0057Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 126
  · exact hroot.hOcc 132
  · exact hroot.hOcc 141
  · exact hroot.hOcc 162
  · exact hroot.hOcc 283
  · exact hroot.hOcc 290
  · exact hroot.hOcc 442
  · exact hroot.hOcc 507
  · exact hroot.hOcc 587
  · exact hroot.hOcc 597
  · exact hroot.hOcc 634
  · exact hroot.hOcc 646
  · exact hroot.hOcc 782
  · exact hroot.hOcc 843
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1217
  · exact hroot.hOcc 1240
  · exact hroot.hOcc 1313
  · exact hroot.hOcc 1369
  · exact hroot.hOcc 1392
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1506
  · exact hroot.hOcc 1517
  · exact hroot.hOcc 1547
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1626
  · exact hroot.hOcc 1655
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18

end QiushiMatmul
