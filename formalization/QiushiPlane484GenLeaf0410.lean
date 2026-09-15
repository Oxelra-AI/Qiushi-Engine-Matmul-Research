import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0410Refs : Fin 43 → RowRef 1665 43 := ![.occ 121, .occ 126, .occ 132, .occ 135, .occ 136, .occ 140, .occ 280, .occ 289, .occ 407, .occ 494, .occ 766, .occ 890, .occ 1039, .occ 1123, .occ 1145, .occ 1164, .occ 1183, .occ 1184, .occ 1214, .occ 1257, .occ 1317, .occ 1343, .occ 1357, .occ 1370, .occ 1408, .occ 1462, .occ 1468, .occ 1489, .occ 1547, .occ 1587, .occ 1606, .occ 1607, .occ 1637, .occ 1654, .sumGe, .nonneg 17, .branchLe 15 (0), .branchGe 2 (1), .branchGe 7 (1), .branchLe 6 (0), .branchLe 31 (0), .branchGe 24 (1), .branchGe 38 (1)]

def plane484GenLeaf0410Mult : Fin 43 → Nat := ![291, 903, 29, 174, 954, 99, 1161, 298, 484, 1, 18, 458, 718, 155, 44, 1127, 12, 31, 22, 12, 66, 571, 8, 32, 1, 56, 294, 33, 160, 210, 8, 88, 12, 133, 1260, 115, 205, 1201, 5363, 68, 1232, 5530, 2567]

theorem plane484GenLeaf0410 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0410Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0410Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0410Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0410Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 126
  · exact hroot.hOcc 132
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 140
  · exact hroot.hOcc 280
  · exact hroot.hOcc 289
  · exact hroot.hOcc 407
  · exact hroot.hOcc 494
  · exact hroot.hOcc 766
  · exact hroot.hOcc 890
  · exact hroot.hOcc 1039
  · exact hroot.hOcc 1123
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1184
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1257
  · exact hroot.hOcc 1317
  · exact hroot.hOcc 1343
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1370
  · exact hroot.hOcc 1408
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1468
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1547
  · exact hroot.hOcc 1587
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1637
  · exact hroot.hOcc 1654
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (31 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24
  · change (∑ k, (if k = (38 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38

end QiushiMatmul
