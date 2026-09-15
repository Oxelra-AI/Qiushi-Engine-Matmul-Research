import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0078Refs : Fin 42 → RowRef 1665 43 := ![.occ 120, .occ 122, .occ 123, .occ 124, .occ 129, .occ 134, .occ 135, .occ 137, .occ 179, .occ 713, .occ 719, .occ 739, .occ 740, .occ 758, .occ 759, .occ 823, .occ 1013, .occ 1220, .occ 1272, .occ 1379, .occ 1414, .occ 1429, .occ 1437, .occ 1458, .occ 1462, .occ 1601, .occ 1602, .occ 1630, .occ 1635, .sumGe, .nonneg 0, .nonneg 2, .branchLe 15 (0), .branchLe 29 (0), .branchLe 4 (0), .branchGe 13 (1), .branchGe 42 (1), .branchLe 9 (0), .branchGe 20 (1), .branchLe 41 (0), .branchLe 37 (0), .branchGe 12 (1)]

def plane484GenLeaf0078Mult : Fin 42 → Nat := ![35, 119, 192, 292, 119, 306, 224, 178, 5, 70, 128, 38, 24, 140, 136, 152, 68, 430, 100, 38, 238, 70, 38, 54, 16, 12, 180, 138, 16, 638, 138, 264, 276, 626, 168, 874, 698, 168, 1458, 638, 442, 832]

theorem plane484GenLeaf0078 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_41 : x 41 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0078Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0078Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0078Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0078Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 129
  · exact hroot.hOcc 134
  · exact hroot.hOcc 135
  · exact hroot.hOcc 137
  · exact hroot.hOcc 179
  · exact hroot.hOcc 713
  · exact hroot.hOcc 719
  · exact hroot.hOcc 739
  · exact hroot.hOcc 740
  · exact hroot.hOcc 758
  · exact hroot.hOcc 759
  · exact hroot.hOcc 823
  · exact hroot.hOcc 1013
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1272
  · exact hroot.hOcc 1379
  · exact hroot.hOcc 1414
  · exact hroot.hOcc 1429
  · exact hroot.hOcc 1437
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1630
  · exact hroot.hOcc 1635
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (9 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20
  · change (∑ k, (if k = (41 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_41
  · change (∑ k, (if k = (37 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (12 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12

end QiushiMatmul
