import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0233Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 121, .occ 123, .occ 125, .occ 127, .occ 130, .occ 135, .occ 136, .occ 554, .occ 730, .occ 766, .occ 1134, .occ 1145, .occ 1150, .occ 1168, .occ 1187, .occ 1200, .occ 1320, .occ 1357, .occ 1416, .occ 1430, .occ 1459, .occ 1484, .occ 1489, .occ 1515, .occ 1606, .occ 1647, .occ 1657, .occ 1663, .sumGe, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchLe 29 (0), .branchLe 17 (0), .branchLe 16 (0), .branchGe 31 (1), .branchLe 20 (0), .branchLe 5 (0), .branchLe 21 (0), .branchLe 28 (0), .branchGe 9 (1)]

def plane484GenLeaf0233Mult : Fin 44 → Nat := ![86, 305, 313, 167, 471, 137, 85, 264, 74, 127, 262, 75, 95, 243, 529, 458, 338, 46, 75, 73, 98, 45, 145, 77, 31, 286, 46, 95, 46, 1159, 516, 904, 196, 362, 482, 1014, 803, 754, 878, 902, 380, 708, 873, 2326]

theorem plane484GenLeaf0233 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0233Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0233Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0233Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0233Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 121
  · exact hroot.hOcc 123
  · exact hroot.hOcc 125
  · exact hroot.hOcc 127
  · exact hroot.hOcc 130
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 554
  · exact hroot.hOcc 730
  · exact hroot.hOcc 766
  · exact hroot.hOcc 1134
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1320
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1416
  · exact hroot.hOcc 1430
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1515
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1647
  · exact hroot.hOcc 1657
  · exact hroot.hOcc 1663
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (21 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (9 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9

end QiushiMatmul
