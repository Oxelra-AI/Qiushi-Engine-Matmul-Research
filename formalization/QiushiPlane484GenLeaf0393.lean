import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0393Refs : Fin 43 → RowRef 1665 43 := ![.occ 119, .occ 121, .occ 124, .occ 126, .occ 127, .occ 134, .occ 136, .occ 137, .occ 138, .occ 139, .occ 318, .occ 507, .occ 508, .occ 707, .occ 777, .occ 778, .occ 838, .occ 843, .occ 858, .occ 1040, .occ 1151, .occ 1166, .occ 1196, .occ 1360, .occ 1379, .occ 1414, .occ 1488, .occ 1489, .occ 1495, .occ 1530, .sumGe, .nonneg 6, .nonneg 13, .branchLe 15 (0), .branchGe 2 (1), .branchGe 7 (1), .branchLe 31 (0), .branchLe 24 (0), .branchLe 37 (0), .branchLe 35 (0), .branchLe 33 (0), .branchLe 11 (0), .branchGe 39 (1)]

def plane484GenLeaf0393Mult : Fin 43 → Nat := ![230, 225, 175, 479, 575, 16, 180, 192, 238, 172, 98, 180, 32, 208, 150, 126, 192, 428, 50, 30, 66, 608, 400, 8, 494, 46, 38, 104, 66, 160, 1054, 132, 112, 766, 868, 3438, 988, 44, 950, 1016, 654, 112, 732]

theorem plane484GenLeaf0393 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0393Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0393Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0393Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0393Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 124
  · exact hroot.hOcc 126
  · exact hroot.hOcc 127
  · exact hroot.hOcc 134
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 139
  · exact hroot.hOcc 318
  · exact hroot.hOcc 507
  · exact hroot.hOcc 508
  · exact hroot.hOcc 707
  · exact hroot.hOcc 777
  · exact hroot.hOcc 778
  · exact hroot.hOcc 838
  · exact hroot.hOcc 843
  · exact hroot.hOcc 858
  · exact hroot.hOcc 1040
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1360
  · exact hroot.hOcc 1379
  · exact hroot.hOcc 1414
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1495
  · exact hroot.hOcc 1530
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (31 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (37 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (33 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (11 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (39 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39

end QiushiMatmul
