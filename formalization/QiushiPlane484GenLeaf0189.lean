import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0189Refs : Fin 44 → RowRef 1665 43 := ![.occ 125, .occ 128, .occ 129, .occ 201, .occ 216, .occ 217, .occ 230, .occ 290, .occ 390, .occ 470, .occ 1025, .occ 1145, .occ 1164, .occ 1214, .occ 1241, .occ 1245, .occ 1259, .occ 1265, .occ 1269, .occ 1280, .occ 1381, .occ 1384, .occ 1397, .occ 1488, .occ 1496, .occ 1516, .occ 1523, .occ 1526, .occ 1562, .occ 1597, .occ 1606, .sumGe, .nonneg 2, .nonneg 14, .branchLe 15 (0), .branchGe 29 (1), .branchGe 35 (1), .branchLe 16 (0), .branchLe 18 (0), .branchLe 1 (0), .branchGe 5 (1), .branchLe 22 (0), .branchLe 30 (0), .branchGe 8 (1)]

def plane484GenLeaf0189Mult : Fin 44 → Nat := ![126, 417, 447, 176, 392, 108, 41, 2, 22, 84, 62, 146, 50, 50, 14, 9, 32, 6, 163, 63, 50, 75, 17, 123, 234, 79, 148, 76, 110, 2, 30, 529, 100, 872, 446, 1084, 1013, 453, 313, 60, 1712, 529, 529, 1719]

theorem plane484GenLeaf0189 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0189Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0189Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0189Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0189Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 125
  · exact hroot.hOcc 128
  · exact hroot.hOcc 129
  · exact hroot.hOcc 201
  · exact hroot.hOcc 216
  · exact hroot.hOcc 217
  · exact hroot.hOcc 230
  · exact hroot.hOcc 290
  · exact hroot.hOcc 390
  · exact hroot.hOcc 470
  · exact hroot.hOcc 1025
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1241
  · exact hroot.hOcc 1245
  · exact hroot.hOcc 1259
  · exact hroot.hOcc 1265
  · exact hroot.hOcc 1269
  · exact hroot.hOcc 1280
  · exact hroot.hOcc 1381
  · exact hroot.hOcc 1384
  · exact hroot.hOcc 1397
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1516
  · exact hroot.hOcc 1523
  · exact hroot.hOcc 1526
  · exact hroot.hOcc 1562
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1606
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8

end QiushiMatmul
