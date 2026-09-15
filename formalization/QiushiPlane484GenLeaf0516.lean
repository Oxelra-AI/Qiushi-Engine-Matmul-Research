import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0516Refs : Fin 42 → RowRef 1665 43 := ![.occ 119, .occ 122, .occ 125, .occ 128, .occ 129, .occ 131, .occ 138, .occ 156, .occ 400, .occ 564, .occ 593, .occ 637, .occ 859, .occ 935, .occ 942, .occ 1186, .occ 1205, .occ 1234, .occ 1279, .occ 1303, .occ 1449, .occ 1528, .occ 1534, .occ 1546, .occ 1564, .occ 1590, .occ 1641, .occ 1645, .occ 1648, .occ 1649, .occ 1663, .sumGe, .nonneg 23, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchLe 26 (0), .branchLe 30 (0), .branchLe 34 (0), .branchGe 8 (1), .branchLe 42 (0), .branchGe 31 (1)]

def plane484GenLeaf0516Mult : Fin 42 → Nat := ![14, 97, 85, 44, 151, 176, 46, 142, 65, 36, 66, 139, 23, 18, 24, 153, 86, 23, 23, 41, 54, 51, 10, 10, 162, 101, 34, 13, 21, 47, 34, 375, 44, 444, 133, 98, 288, 289, 375, 1105, 287, 667]

theorem plane484GenLeaf0516 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0516Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0516Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0516Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0516Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 122
  · exact hroot.hOcc 125
  · exact hroot.hOcc 128
  · exact hroot.hOcc 129
  · exact hroot.hOcc 131
  · exact hroot.hOcc 138
  · exact hroot.hOcc 156
  · exact hroot.hOcc 400
  · exact hroot.hOcc 564
  · exact hroot.hOcc 593
  · exact hroot.hOcc 637
  · exact hroot.hOcc 859
  · exact hroot.hOcc 935
  · exact hroot.hOcc 942
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1234
  · exact hroot.hOcc 1279
  · exact hroot.hOcc 1303
  · exact hroot.hOcc 1449
  · exact hroot.hOcc 1528
  · exact hroot.hOcc 1534
  · exact hroot.hOcc 1546
  · exact hroot.hOcc 1564
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1641
  · exact hroot.hOcc 1645
  · exact hroot.hOcc 1648
  · exact hroot.hOcc 1649
  · exact hroot.hOcc 1663
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31

end QiushiMatmul
