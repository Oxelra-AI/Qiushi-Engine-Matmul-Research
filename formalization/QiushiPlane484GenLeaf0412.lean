import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0412Refs : Fin 42 → RowRef 1665 43 := ![.occ 121, .occ 124, .occ 145, .occ 440, .occ 469, .occ 472, .occ 505, .occ 507, .occ 510, .occ 782, .occ 841, .occ 1133, .occ 1146, .occ 1168, .occ 1172, .occ 1183, .occ 1188, .occ 1208, .occ 1376, .occ 1467, .occ 1486, .occ 1489, .occ 1571, .occ 1590, .occ 1597, .occ 1607, .occ 1608, .occ 1618, .occ 1634, .sumGe, .nonneg 8, .branchLe 15 (0), .branchGe 2 (1), .branchGe 7 (1), .branchLe 6 (0), .branchGe 31 (1), .branchLe 29 (0), .branchLe 14 (0), .branchLe 24 (0), .branchLe 22 (0), .branchLe 16 (0), .branchGe 41 (1)]

def plane484GenLeaf0412Mult : Fin 42 → Nat := ![213, 249, 112, 211, 143, 125, 45, 138, 405, 71, 101, 30, 6, 3, 19, 259, 25, 84, 114, 55, 71, 46, 2, 194, 19, 110, 117, 234, 11, 595, 24, 291, 74, 2201, 578, 804, 273, 540, 595, 503, 500, 915]

theorem plane484GenLeaf0412 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_41 : (1 : Int) ≤ x 41)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0412Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0412Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0412Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0412Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 124
  · exact hroot.hOcc 145
  · exact hroot.hOcc 440
  · exact hroot.hOcc 469
  · exact hroot.hOcc 472
  · exact hroot.hOcc 505
  · exact hroot.hOcc 507
  · exact hroot.hOcc 510
  · exact hroot.hOcc 782
  · exact hroot.hOcc 841
  · exact hroot.hOcc 1133
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1376
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1618
  · exact hroot.hOcc 1634
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (41 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_41

end QiushiMatmul
