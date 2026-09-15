import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0414Refs : Fin 43 → RowRef 1665 43 := ![.occ 119, .occ 121, .occ 132, .occ 136, .occ 137, .occ 138, .occ 140, .occ 142, .occ 233, .occ 289, .occ 475, .occ 633, .occ 634, .occ 778, .occ 860, .occ 1134, .occ 1146, .occ 1172, .occ 1174, .occ 1183, .occ 1186, .occ 1187, .occ 1196, .occ 1238, .occ 1270, .occ 1571, .occ 1590, .occ 1608, .occ 1647, .occ 1657, .sumGe, .nonneg 9, .nonneg 10, .nonneg 19, .branchLe 15 (0), .branchGe 2 (1), .branchGe 7 (1), .branchLe 6 (0), .branchGe 31 (1), .branchLe 29 (0), .branchLe 14 (0), .branchLe 24 (0), .branchGe 22 (1)]

def plane484GenLeaf0414Mult : Fin 43 → Nat := ![124, 120, 75, 76, 24, 46, 9, 41, 56, 156, 48, 88, 20, 244, 79, 48, 4, 4, 28, 92, 60, 60, 60, 16, 4, 144, 44, 52, 32, 16, 296, 36, 188, 170, 108, 506, 996, 260, 200, 108, 260, 104, 778]

theorem plane484GenLeaf0414 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0414Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0414Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0414Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0414Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 132
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 140
  · exact hroot.hOcc 142
  · exact hroot.hOcc 233
  · exact hroot.hOcc 289
  · exact hroot.hOcc 475
  · exact hroot.hOcc 633
  · exact hroot.hOcc 634
  · exact hroot.hOcc 778
  · exact hroot.hOcc 860
  · exact hroot.hOcc 1134
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1238
  · exact hroot.hOcc 1270
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1647
  · exact hroot.hOcc 1657
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (9 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22

end QiushiMatmul
