import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0471Refs : Fin 44 → RowRef 1665 43 := ![.occ 85, .occ 121, .occ 129, .occ 133, .occ 142, .occ 171, .occ 330, .occ 518, .occ 532, .occ 547, .occ 596, .occ 615, .occ 739, .occ 853, .occ 1109, .occ 1113, .occ 1136, .occ 1158, .occ 1159, .occ 1188, .occ 1206, .occ 1250, .occ 1394, .occ 1447, .occ 1454, .occ 1573, .occ 1580, .occ 1601, .occ 1602, .occ 1610, .occ 1642, .sumGe, .nonneg 19, .nonneg 20, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchGe 0 (1), .branchLe 25 (0), .branchLe 3 (0), .branchLe 38 (0), .branchLe 27 (0), .branchGe 34 (1), .branchGe 41 (1)]

def plane484GenLeaf0471Mult : Fin 44 → Nat := ![1079, 482, 868, 4248, 5786, 230, 1600, 966, 2080, 1514, 2089, 482, 88, 147, 1230, 1563, 838, 160, 2970, 5100, 4705, 542, 6275, 533, 1624, 480, 2, 433, 1320, 243, 3706, 10516, 791, 1269, 31132, 2201, 4927, 5747, 482, 7633, 10273, 5416, 26972, 15242]

theorem plane484GenLeaf0471 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_41 : (1 : Int) ≤ x 41)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0471Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0471Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0471Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0471Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 85
  · exact hroot.hOcc 121
  · exact hroot.hOcc 129
  · exact hroot.hOcc 133
  · exact hroot.hOcc 142
  · exact hroot.hOcc 171
  · exact hroot.hOcc 330
  · exact hroot.hOcc 518
  · exact hroot.hOcc 532
  · exact hroot.hOcc 547
  · exact hroot.hOcc 596
  · exact hroot.hOcc 615
  · exact hroot.hOcc 739
  · exact hroot.hOcc 853
  · exact hroot.hOcc 1109
  · exact hroot.hOcc 1113
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1250
  · exact hroot.hOcc 1394
  · exact hroot.hOcc 1447
  · exact hroot.hOcc 1454
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1642
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (38 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (27 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (41 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_41

end QiushiMatmul
