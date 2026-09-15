import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0292Refs : Fin 43 → RowRef 1665 43 := ![.occ 119, .occ 123, .occ 126, .occ 130, .occ 144, .occ 195, .occ 552, .occ 695, .occ 807, .occ 1143, .occ 1145, .occ 1147, .occ 1160, .occ 1179, .occ 1214, .occ 1304, .occ 1306, .occ 1353, .occ 1420, .occ 1471, .occ 1488, .occ 1491, .occ 1495, .occ 1571, .occ 1597, .occ 1602, .occ 1628, .occ 1656, .sumGe, .nonneg 4, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchGe 29 (1), .branchGe 34 (1), .branchLe 36 (0), .branchLe 22 (0), .branchLe 32 (0), .branchLe 17 (0), .branchLe 20 (0), .branchGe 3 (1)]

def plane484GenLeaf0292Mult : Fin 43 → Nat := ![359, 402, 728, 273, 260, 765, 940, 172, 450, 27, 215, 180, 849, 90, 27, 103, 10, 126, 409, 125, 91, 296, 65, 29, 482, 64, 171, 516, 1671, 52, 1568, 362, 124, 1401, 777, 1428, 3015, 642, 1516, 1580, 822, 1516, 4819]

theorem plane484GenLeaf0292 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0292Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0292Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0292Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0292Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 123
  · exact hroot.hOcc 126
  · exact hroot.hOcc 130
  · exact hroot.hOcc 144
  · exact hroot.hOcc 195
  · exact hroot.hOcc 552
  · exact hroot.hOcc 695
  · exact hroot.hOcc 807
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1304
  · exact hroot.hOcc 1306
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1420
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1495
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1628
  · exact hroot.hOcc 1656
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
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
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3

end QiushiMatmul
