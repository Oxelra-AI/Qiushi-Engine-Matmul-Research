import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0071Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 122, .occ 131, .occ 132, .occ 133, .occ 139, .occ 141, .occ 142, .occ 568, .occ 718, .occ 740, .occ 741, .occ 1060, .occ 1173, .occ 1179, .occ 1190, .occ 1213, .occ 1214, .occ 1278, .occ 1377, .occ 1379, .occ 1458, .occ 1459, .occ 1462, .occ 1470, .occ 1537, .occ 1600, .occ 1602, .occ 1606, .occ 1610, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchGe 13 (1), .branchGe 42 (1), .branchLe 9 (0), .branchLe 20 (0), .branchLe 7 (0), .branchLe 8 (0), .branchLe 3 (0), .branchLe 27 (0), .branchGe 0 (1)]

def plane484GenLeaf0071Mult : Fin 44 → Nat := ![25434, 1306, 12942, 7137, 1675, 4287, 964, 10593, 3980, 998, 6080, 12084, 1502, 18578, 5924, 2854, 540, 7096, 2328, 2186, 1448, 5066, 3368, 5190, 7818, 2094, 8862, 12038, 5618, 13202, 42270, 14874, 39416, 29250, 38870, 37410, 41688, 8890, 5370, 38636, 33146, 42270, 20828, 73098]

theorem plane484GenLeaf0071 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0071Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0071Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0071Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0071Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 122
  · exact hroot.hOcc 131
  · exact hroot.hOcc 132
  · exact hroot.hOcc 133
  · exact hroot.hOcc 139
  · exact hroot.hOcc 141
  · exact hroot.hOcc 142
  · exact hroot.hOcc 568
  · exact hroot.hOcc 718
  · exact hroot.hOcc 740
  · exact hroot.hOcc 741
  · exact hroot.hOcc 1060
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1278
  · exact hroot.hOcc 1377
  · exact hroot.hOcc 1379
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1537
  · exact hroot.hOcc 1600
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1610
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (9 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (27 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
