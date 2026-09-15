import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0283Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 125, .occ 127, .occ 135, .occ 148, .occ 368, .occ 384, .occ 425, .occ 551, .occ 653, .occ 707, .occ 1136, .occ 1140, .occ 1143, .occ 1150, .occ 1151, .occ 1160, .occ 1170, .occ 1180, .occ 1223, .occ 1238, .occ 1462, .occ 1481, .occ 1488, .occ 1492, .occ 1496, .occ 1548, .occ 1609, .occ 1615, .occ 1640, .sumGe, .nonneg 14, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchGe 29 (1), .branchLe 34 (0), .branchLe 13 (0), .branchGe 37 (1), .branchGe 32 (1), .branchLe 10 (0), .branchGe 4 (1)]

def plane484GenLeaf0283Mult : Fin 44 → Nat := ![550, 26286, 5838, 4362, 13128, 24779, 3068, 553, 22780, 98, 5982, 10661, 6323, 979, 559, 21915, 7057, 10246, 7295, 5288, 5113, 11362, 3355, 8313, 11151, 315, 7600, 6534, 4967, 5560, 45997, 6404, 31108, 21619, 26896, 45682, 23225, 82008, 18987, 45997, 60650, 104843, 45997, 68250]

theorem plane484GenLeaf0283 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0283Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0283Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0283Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0283Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 125
  · exact hroot.hOcc 127
  · exact hroot.hOcc 135
  · exact hroot.hOcc 148
  · exact hroot.hOcc 368
  · exact hroot.hOcc 384
  · exact hroot.hOcc 425
  · exact hroot.hOcc 551
  · exact hroot.hOcc 653
  · exact hroot.hOcc 707
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1180
  · exact hroot.hOcc 1223
  · exact hroot.hOcc 1238
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1548
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1640
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37
  · change (∑ k, (if k = (32 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
