import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0311Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 123, .occ 124, .occ 127, .occ 136, .occ 180, .occ 261, .occ 350, .occ 568, .occ 723, .occ 734, .occ 768, .occ 1136, .occ 1140, .occ 1143, .occ 1145, .occ 1191, .occ 1216, .occ 1353, .occ 1422, .occ 1462, .occ 1471, .occ 1472, .occ 1477, .occ 1481, .occ 1486, .occ 1488, .occ 1491, .occ 1538, .occ 1557, .occ 1601, .occ 1609, .occ 1638, .sumGe, .nonneg 31, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchGe 29 (1), .branchGe 34 (1), .branchGe 36 (1), .branchGe 42 (1)]

def plane484GenLeaf0311Mult : Fin 44 → Nat := ![664, 90, 1420, 588, 1214, 1700, 818, 1688, 1522, 538, 1422, 446, 523, 198, 766, 448, 1342, 537, 3060, 172, 442, 2868, 1768, 1742, 1840, 1050, 2606, 4222, 77, 633, 2522, 300, 342, 7606, 2006, 7606, 9434, 4548, 7606, 5994, 15308, 10398, 17118, 14674]

theorem plane484GenLeaf0311 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0311Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0311Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0311Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0311Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 127
  · exact hroot.hOcc 136
  · exact hroot.hOcc 180
  · exact hroot.hOcc 261
  · exact hroot.hOcc 350
  · exact hroot.hOcc 568
  · exact hroot.hOcc 723
  · exact hroot.hOcc 734
  · exact hroot.hOcc 768
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1422
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1538
  · exact hroot.hOcc 1557
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1638
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 31
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (36 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42

end QiushiMatmul
