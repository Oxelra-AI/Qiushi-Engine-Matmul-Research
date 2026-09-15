import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0407Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 121, .occ 126, .occ 127, .occ 129, .occ 133, .occ 135, .occ 137, .occ 139, .occ 508, .occ 842, .occ 932, .occ 1119, .occ 1136, .occ 1166, .occ 1172, .occ 1173, .occ 1174, .occ 1191, .occ 1196, .occ 1353, .occ 1375, .occ 1446, .occ 1472, .occ 1486, .occ 1488, .occ 1489, .occ 1571, .occ 1597, .occ 1607, .sumGe, .nonneg 12, .nonneg 19, .branchLe 15 (0), .branchGe 2 (1), .branchGe 7 (1), .branchLe 6 (0), .branchLe 31 (0), .branchLe 24 (0), .branchGe 37 (1), .branchGe 0 (1), .branchLe 5 (0), .branchGe 1 (1), .branchGe 21 (1)]

def plane484GenLeaf0407Mult : Fin 44 → Nat := ![141, 133, 70, 147, 83, 152, 62, 168, 192, 166, 84, 54, 26, 52, 54, 64, 64, 66, 2, 116, 84, 56, 62, 8, 152, 22, 60, 64, 24, 68, 428, 34, 164, 152, 314, 1114, 128, 428, 64, 282, 182, 98, 294, 926]

theorem plane484GenLeaf0407 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0407Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0407Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0407Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0407Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 126
  · exact hroot.hOcc 127
  · exact hroot.hOcc 129
  · exact hroot.hOcc 133
  · exact hroot.hOcc 135
  · exact hroot.hOcc 137
  · exact hroot.hOcc 139
  · exact hroot.hOcc 508
  · exact hroot.hOcc 842
  · exact hroot.hOcc 932
  · exact hroot.hOcc 1119
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1375
  · exact hroot.hOcc 1446
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1607
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (12 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (31 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21

end QiushiMatmul
