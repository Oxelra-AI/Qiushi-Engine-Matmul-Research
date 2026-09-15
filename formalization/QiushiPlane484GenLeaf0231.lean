import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0231Refs : Fin 44 → RowRef 1665 43 := ![.occ 84, .occ 86, .occ 116, .occ 118, .occ 122, .occ 123, .occ 126, .occ 207, .occ 1113, .occ 1134, .occ 1145, .occ 1172, .occ 1179, .occ 1187, .occ 1200, .occ 1320, .occ 1430, .occ 1459, .occ 1470, .occ 1477, .occ 1483, .occ 1486, .occ 1553, .occ 1602, .occ 1609, .occ 1618, .occ 1647, .occ 1648, .sumGe, .branchLe 15 (0), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchLe 29 (0), .branchLe 17 (0), .branchLe 16 (0), .branchGe 31 (1), .branchLe 20 (0), .branchLe 30 (0), .branchLe 5 (0), .branchLe 21 (0), .branchLe 28 (0), .branchLe 9 (0), .branchLe 24 (0)]

def plane484GenLeaf0231Mult : Fin 44 → Nat := ![5538, 261, 1816, 111, 8624, 4438, 1636, 601, 1722, 1175, 848, 4812, 9747, 1850, 2045, 2748, 709, 658, 3803, 8230, 4530, 7818, 1109, 3641, 1784, 11749, 3831, 2630, 31173, 20793, 3509, 16136, 18249, 13608, 12700, 23539, 9754, 4923, 26620, 28541, 23731, 23002, 20415, 23864]

theorem plane484GenLeaf0231 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0231Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0231Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0231Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0231Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 84
  · exact hroot.hOcc 86
  · exact hroot.hOcc 116
  · exact hroot.hOcc 118
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 126
  · exact hroot.hOcc 207
  · exact hroot.hOcc 1113
  · exact hroot.hOcc 1134
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1320
  · exact hroot.hOcc 1430
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1553
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1618
  · exact hroot.hOcc 1647
  · exact hroot.hOcc 1648
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (21 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (9 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24

end QiushiMatmul
