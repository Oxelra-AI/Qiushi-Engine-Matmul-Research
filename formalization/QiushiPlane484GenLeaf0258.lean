import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0258Refs : Fin 43 → RowRef 1665 43 := ![.occ 119, .occ 122, .occ 123, .occ 125, .occ 128, .occ 129, .occ 132, .occ 136, .occ 189, .occ 1143, .occ 1145, .occ 1187, .occ 1190, .occ 1205, .occ 1245, .occ 1308, .occ 1340, .occ 1342, .occ 1385, .occ 1435, .occ 1449, .occ 1450, .occ 1462, .occ 1470, .occ 1489, .occ 1562, .occ 1567, .occ 1608, .occ 1609, .sumGe, .nonneg 5, .nonneg 19, .nonneg 22, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchLe 29 (0), .branchGe 17 (1), .branchLe 3 (0), .branchLe 20 (0), .branchGe 8 (1)]

def plane484GenLeaf0258Mult : Fin 43 → Nat := ![190, 253, 935, 311, 307, 486, 962, 682, 856, 190, 90, 602, 250, 652, 150, 20, 150, 340, 20, 30, 376, 364, 30, 712, 106, 222, 310, 36, 280, 1954, 220, 116, 292, 1132, 1522, 1242, 276, 1888, 1644, 3540, 280, 1848, 5134]

theorem plane484GenLeaf0258 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0258Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0258Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0258Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0258Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 125
  · exact hroot.hOcc 128
  · exact hroot.hOcc 129
  · exact hroot.hOcc 132
  · exact hroot.hOcc 136
  · exact hroot.hOcc 189
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1245
  · exact hroot.hOcc 1308
  · exact hroot.hOcc 1340
  · exact hroot.hOcc 1342
  · exact hroot.hOcc 1385
  · exact hroot.hOcc 1435
  · exact hroot.hOcc 1449
  · exact hroot.hOcc 1450
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1562
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1609
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8

end QiushiMatmul
