import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0526Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 121, .occ 122, .occ 128, .occ 134, .occ 135, .occ 138, .occ 139, .occ 140, .occ 227, .occ 296, .occ 329, .occ 330, .occ 573, .occ 597, .occ 615, .occ 677, .occ 1106, .occ 1124, .occ 1159, .occ 1160, .occ 1179, .occ 1188, .occ 1200, .occ 1206, .occ 1444, .occ 1467, .occ 1471, .occ 1478, .occ 1483, .occ 1484, .occ 1590, .occ 1597, .occ 1610, .sumGe, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchLe 26 (0), .branchLe 30 (0), .branchGe 34 (1), .branchLe 9 (0), .branchGe 18 (1), .branchGe 1 (1)]

def plane484GenLeaf0526Mult : Fin 44 → Nat := ![150, 69, 635, 150, 368, 151, 77, 550, 225, 76, 464, 75, 465, 2, 1026, 391, 450, 74, 448, 345, 276, 258, 94, 758, 345, 148, 224, 54, 573, 94, 534, 91, 615, 155, 1782, 2236, 3870, 930, 930, 654, 2024, 1398, 3418, 2898]

theorem plane484GenLeaf0526 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0526Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0526Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0526Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0526Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 128
  · exact hroot.hOcc 134
  · exact hroot.hOcc 135
  · exact hroot.hOcc 138
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 227
  · exact hroot.hOcc 296
  · exact hroot.hOcc 329
  · exact hroot.hOcc 330
  · exact hroot.hOcc 573
  · exact hroot.hOcc 597
  · exact hroot.hOcc 615
  · exact hroot.hOcc 677
  · exact hroot.hOcc 1106
  · exact hroot.hOcc 1124
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1444
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1610
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (9 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1

end QiushiMatmul
