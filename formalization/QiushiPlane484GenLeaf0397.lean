import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0397Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 121, .occ 124, .occ 134, .occ 137, .occ 143, .occ 179, .occ 445, .occ 597, .occ 707, .occ 840, .occ 1164, .occ 1166, .occ 1168, .occ 1172, .occ 1196, .occ 1208, .occ 1237, .occ 1259, .occ 1293, .occ 1438, .occ 1445, .occ 1458, .occ 1477, .occ 1483, .occ 1486, .occ 1488, .occ 1571, .occ 1597, .occ 1607, .occ 1627, .occ 1638, .sumGe, .nonneg 10, .branchLe 15 (0), .branchGe 2 (1), .branchGe 7 (1), .branchLe 6 (0), .branchLe 31 (0), .branchLe 24 (0), .branchLe 37 (0), .branchGe 35 (1), .branchLe 30 (0), .branchGe 27 (1)]

def plane484GenLeaf0397Mult : Fin 44 → Nat := ![30070, 61825, 72715, 32766, 148518, 164465, 79179, 20326, 54240, 45390, 91306, 89776, 47934, 10418, 29532, 39132, 78966, 12926, 62674, 29578, 13106, 32200, 222, 3402, 75654, 26602, 26194, 46942, 59368, 79202, 16594, 59146, 332322, 41058, 210496, 327046, 804330, 85276, 332322, 118872, 258778, 419270, 75654, 149000]

theorem plane484GenLeaf0397 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0397Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0397Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0397Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0397Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 124
  · exact hroot.hOcc 134
  · exact hroot.hOcc 137
  · exact hroot.hOcc 143
  · exact hroot.hOcc 179
  · exact hroot.hOcc 445
  · exact hroot.hOcc 597
  · exact hroot.hOcc 707
  · exact hroot.hOcc 840
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1237
  · exact hroot.hOcc 1259
  · exact hroot.hOcc 1293
  · exact hroot.hOcc 1438
  · exact hroot.hOcc 1445
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1627
  · exact hroot.hOcc 1638
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (31 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (37 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (27 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27

end QiushiMatmul
