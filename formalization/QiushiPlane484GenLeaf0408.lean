import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0408Refs : Fin 42 → RowRef 1665 43 := ![.occ 121, .occ 124, .occ 126, .occ 129, .occ 137, .occ 141, .occ 142, .occ 232, .occ 325, .occ 781, .occ 842, .occ 1136, .occ 1145, .occ 1166, .occ 1174, .occ 1196, .occ 1257, .occ 1346, .occ 1353, .occ 1375, .occ 1486, .occ 1531, .occ 1532, .occ 1533, .occ 1571, .occ 1607, .occ 1609, .sumGe, .nonneg 4, .nonneg 6, .nonneg 8, .nonneg 10, .nonneg 13, .nonneg 17, .branchLe 15 (0), .branchGe 2 (1), .branchGe 7 (1), .branchLe 31 (0), .branchLe 24 (0), .branchGe 37 (1), .branchGe 0 (1), .branchGe 5 (1)]

def plane484GenLeaf0408Mult : Fin 42 → Nat := ![192, 196, 4, 224, 95, 51, 3, 20, 23, 10, 18, 32, 6, 54, 36, 48, 34, 2, 32, 26, 78, 22, 34, 60, 32, 56, 58, 228, 6, 58, 106, 130, 562, 64, 202, 254, 918, 228, 140, 178, 282, 626]

theorem plane484GenLeaf0408 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0408Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0408Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0408Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0408Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 124
  · exact hroot.hOcc 126
  · exact hroot.hOcc 129
  · exact hroot.hOcc 137
  · exact hroot.hOcc 141
  · exact hroot.hOcc 142
  · exact hroot.hOcc 232
  · exact hroot.hOcc 325
  · exact hroot.hOcc 781
  · exact hroot.hOcc 842
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1257
  · exact hroot.hOcc 1346
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1375
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1531
  · exact hroot.hOcc 1532
  · exact hroot.hOcc 1533
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1609
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (31 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5

end QiushiMatmul
