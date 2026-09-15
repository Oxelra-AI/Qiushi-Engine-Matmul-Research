import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0100Refs : Fin 43 → RowRef 1665 43 := ![.occ 119, .occ 125, .occ 127, .occ 130, .occ 140, .occ 142, .occ 281, .occ 282, .occ 289, .occ 340, .occ 384, .occ 708, .occ 724, .occ 812, .occ 900, .occ 963, .occ 992, .occ 1043, .occ 1120, .occ 1145, .occ 1146, .occ 1147, .occ 1150, .occ 1254, .occ 1408, .occ 1573, .occ 1606, .occ 1608, .occ 1620, .occ 1628, .occ 1639, .occ 1659, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchGe 4 (1), .branchLe 36 (0), .branchGe 26 (1), .branchGe 37 (1), .branchLe 34 (0), .branchLe 16 (0), .branchLe 12 (0)]

def plane484GenLeaf0100Mult : Fin 43 → Nat := ![635, 43, 368, 25, 1602, 384, 890, 368, 259, 930, 924, 366, 610, 128, 1454, 416, 1168, 98, 280, 710, 468, 60, 950, 14, 950, 468, 608, 342, 802, 426, 512, 184, 3346, 1078, 546, 3346, 7068, 2878, 6262, 8118, 2576, 1840, 1900]

theorem plane484GenLeaf0100 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0100Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0100Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0100Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0100Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 125
  · exact hroot.hOcc 127
  · exact hroot.hOcc 130
  · exact hroot.hOcc 140
  · exact hroot.hOcc 142
  · exact hroot.hOcc 281
  · exact hroot.hOcc 282
  · exact hroot.hOcc 289
  · exact hroot.hOcc 340
  · exact hroot.hOcc 384
  · exact hroot.hOcc 708
  · exact hroot.hOcc 724
  · exact hroot.hOcc 812
  · exact hroot.hOcc 900
  · exact hroot.hOcc 963
  · exact hroot.hOcc 992
  · exact hroot.hOcc 1043
  · exact hroot.hOcc 1120
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1254
  · exact hroot.hOcc 1408
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1620
  · exact hroot.hOcc 1628
  · exact hroot.hOcc 1639
  · exact hroot.hOcc 1659
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (12 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12

end QiushiMatmul
