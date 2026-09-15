import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0090Refs : Fin 42 → RowRef 1665 43 := ![.occ 119, .occ 120, .occ 122, .occ 126, .occ 127, .occ 129, .occ 134, .occ 175, .occ 329, .occ 380, .occ 656, .occ 917, .occ 1146, .occ 1150, .occ 1160, .occ 1243, .occ 1256, .occ 1277, .occ 1408, .occ 1442, .occ 1450, .occ 1472, .occ 1478, .occ 1506, .occ 1510, .occ 1577, .occ 1597, .occ 1598, .occ 1609, .occ 1610, .occ 1644, .sumGe, .nonneg 1, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchGe 4 (1), .branchLe 36 (0), .branchLe 26 (0), .branchLe 24 (0), .branchGe 19 (1), .branchGe 6 (1)]

def plane484GenLeaf0090Mult : Fin 42 → Nat := ![187, 103, 482, 82, 506, 91, 428, 187, 136, 36, 150, 88, 48, 634, 66, 118, 85, 69, 23, 89, 56, 174, 292, 69, 139, 74, 84, 32, 208, 186, 94, 1028, 1740, 892, 730, 962, 1674, 770, 980, 772, 670, 2196]

theorem plane484GenLeaf0090 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0090Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0090Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0090Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0090Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 120
  · exact hroot.hOcc 122
  · exact hroot.hOcc 126
  · exact hroot.hOcc 127
  · exact hroot.hOcc 129
  · exact hroot.hOcc 134
  · exact hroot.hOcc 175
  · exact hroot.hOcc 329
  · exact hroot.hOcc 380
  · exact hroot.hOcc 656
  · exact hroot.hOcc 917
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1243
  · exact hroot.hOcc 1256
  · exact hroot.hOcc 1277
  · exact hroot.hOcc 1408
  · exact hroot.hOcc 1442
  · exact hroot.hOcc 1450
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1506
  · exact hroot.hOcc 1510
  · exact hroot.hOcc 1577
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1598
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1644
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6

end QiushiMatmul
