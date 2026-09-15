import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0416Refs : Fin 43 → RowRef 1665 43 := ![.occ 121, .occ 124, .occ 126, .occ 135, .occ 136, .occ 139, .occ 140, .occ 154, .occ 280, .occ 443, .occ 444, .occ 448, .occ 505, .occ 779, .occ 804, .occ 882, .occ 1145, .occ 1147, .occ 1164, .occ 1166, .occ 1183, .occ 1208, .occ 1214, .occ 1351, .occ 1357, .occ 1443, .occ 1466, .occ 1571, .occ 1606, .occ 1607, .occ 1628, .occ 1663, .sumGe, .nonneg 4, .branchLe 15 (0), .branchGe 2 (1), .branchGe 7 (1), .branchLe 6 (0), .branchGe 31 (1), .branchLe 29 (0), .branchLe 14 (0), .branchGe 24 (1), .branchGe 34 (1)]

def plane484GenLeaf0416Mult : Fin 43 → Nat := ![133, 339, 102, 242, 479, 99, 155, 476, 715, 187, 126, 369, 413, 45, 123, 295, 115, 44, 126, 130, 35, 35, 141, 26, 264, 35, 50, 35, 105, 44, 267, 211, 880, 115, 483, 511, 2919, 734, 1359, 413, 778, 3345, 765]

theorem plane484GenLeaf0416 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0416Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0416Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0416Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0416Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 124
  · exact hroot.hOcc 126
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 154
  · exact hroot.hOcc 280
  · exact hroot.hOcc 443
  · exact hroot.hOcc 444
  · exact hroot.hOcc 448
  · exact hroot.hOcc 505
  · exact hroot.hOcc 779
  · exact hroot.hOcc 804
  · exact hroot.hOcc 882
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1351
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1443
  · exact hroot.hOcc 1466
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1628
  · exact hroot.hOcc 1663
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34

end QiushiMatmul
