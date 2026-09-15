import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0424Refs : Fin 43 → RowRef 1665 43 := ![.occ 119, .occ 121, .occ 124, .occ 126, .occ 132, .occ 134, .occ 181, .occ 190, .occ 441, .occ 510, .occ 723, .occ 751, .occ 765, .occ 778, .occ 782, .occ 841, .occ 1151, .occ 1164, .occ 1166, .occ 1179, .occ 1186, .occ 1208, .occ 1240, .occ 1244, .occ 1444, .occ 1448, .occ 1486, .occ 1488, .occ 1491, .occ 1571, .occ 1607, .occ 1608, .occ 1628, .sumGe, .branchLe 15 (0), .branchGe 2 (1), .branchGe 7 (1), .branchLe 6 (0), .branchGe 31 (1), .branchGe 29 (1), .branchLe 36 (0), .branchGe 34 (1), .branchGe 42 (1)]

def plane484GenLeaf0424Mult : Fin 43 → Nat := ![673, 64, 2647, 1416, 1063, 151, 3395, 2973, 337, 2101, 4928, 511, 540, 753, 4474, 259, 679, 387, 703, 726, 558, 1091, 92, 47, 314, 1085, 770, 458, 558, 704, 1474, 1237, 2826, 5537, 5537, 1574, 20843, 2884, 11625, 10744, 4276, 12018, 14391]

theorem plane484GenLeaf0424 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0424Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0424Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0424Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0424Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 124
  · exact hroot.hOcc 126
  · exact hroot.hOcc 132
  · exact hroot.hOcc 134
  · exact hroot.hOcc 181
  · exact hroot.hOcc 190
  · exact hroot.hOcc 441
  · exact hroot.hOcc 510
  · exact hroot.hOcc 723
  · exact hroot.hOcc 751
  · exact hroot.hOcc 765
  · exact hroot.hOcc 778
  · exact hroot.hOcc 782
  · exact hroot.hOcc 841
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1240
  · exact hroot.hOcc 1244
  · exact hroot.hOcc 1444
  · exact hroot.hOcc 1448
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1628
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42

end QiushiMatmul
