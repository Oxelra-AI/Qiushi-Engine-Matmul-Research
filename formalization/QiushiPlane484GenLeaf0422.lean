import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0422Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 124, .occ 134, .occ 136, .occ 138, .occ 143, .occ 144, .occ 146, .occ 181, .occ 190, .occ 213, .occ 233, .occ 386, .occ 505, .occ 707, .occ 1109, .occ 1143, .occ 1160, .occ 1164, .occ 1174, .occ 1179, .occ 1186, .occ 1208, .occ 1214, .occ 1240, .occ 1551, .occ 1558, .occ 1567, .occ 1571, .occ 1607, .occ 1608, .occ 1642, .sumGe, .nonneg 4, .branchLe 15 (0), .branchGe 2 (1), .branchGe 7 (1), .branchLe 6 (0), .branchGe 31 (1), .branchGe 29 (1), .branchLe 36 (0), .branchGe 34 (1), .branchLe 42 (0), .branchLe 21 (0)]

def plane484GenLeaf0422Mult : Fin 44 → Nat := ![998, 1550, 415, 885, 362, 412, 313, 371, 1385, 933, 106, 83, 642, 1055, 519, 813, 617, 490, 1129, 1262, 594, 196, 47, 715, 151, 47, 715, 95, 1284, 110, 100, 53, 3346, 1326, 2931, 3563, 6240, 2934, 2013, 4412, 3346, 5045, 3136, 2704]

theorem plane484GenLeaf0422 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0422Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0422Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0422Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0422Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 124
  · exact hroot.hOcc 134
  · exact hroot.hOcc 136
  · exact hroot.hOcc 138
  · exact hroot.hOcc 143
  · exact hroot.hOcc 144
  · exact hroot.hOcc 146
  · exact hroot.hOcc 181
  · exact hroot.hOcc 190
  · exact hroot.hOcc 213
  · exact hroot.hOcc 233
  · exact hroot.hOcc 386
  · exact hroot.hOcc 505
  · exact hroot.hOcc 707
  · exact hroot.hOcc 1109
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1240
  · exact hroot.hOcc 1551
  · exact hroot.hOcc 1558
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1642
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (21 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21

end QiushiMatmul
