import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0483Refs : Fin 39 → RowRef 1665 43 := ![.occ 131, .occ 138, .occ 140, .occ 142, .occ 186, .occ 191, .occ 408, .occ 447, .occ 457, .occ 674, .occ 693, .occ 762, .occ 1159, .occ 1188, .occ 1206, .occ 1216, .occ 1339, .occ 1353, .occ 1358, .occ 1480, .occ 1483, .occ 1590, .occ 1629, .occ 1637, .occ 1660, .sumGe, .nonneg 11, .nonneg 22, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchGe 0 (1), .branchLe 19 (0), .branchLe 25 (0), .branchLe 3 (0), .branchGe 38 (1), .branchGe 34 (1), .branchGe 28 (1), .branchGe 29 (1)]

def plane484GenLeaf0483Mult : Fin 39 → Nat := ![2, 1, 4, 6, 5, 12, 1, 3, 2, 16, 11, 1, 3, 7, 4, 3, 5, 6, 4, 4, 3, 8, 3, 4, 4, 19, 2, 2, 88, 9, 11, 9, 5, 3, 12, 42, 32, 24, 45]

theorem plane484GenLeaf0483 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0483Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0483Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0483Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0483Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 131
  · exact hroot.hOcc 138
  · exact hroot.hOcc 140
  · exact hroot.hOcc 142
  · exact hroot.hOcc 186
  · exact hroot.hOcc 191
  · exact hroot.hOcc 408
  · exact hroot.hOcc 447
  · exact hroot.hOcc 457
  · exact hroot.hOcc 674
  · exact hroot.hOcc 693
  · exact hroot.hOcc 762
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1339
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1480
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1629
  · exact hroot.hOcc 1637
  · exact hroot.hOcc 1660
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (38 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29

end QiushiMatmul
