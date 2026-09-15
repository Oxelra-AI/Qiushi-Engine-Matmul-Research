import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0329Refs : Fin 42 → RowRef 1665 43 := ![.occ 121, .occ 123, .occ 124, .occ 125, .occ 137, .occ 140, .occ 141, .occ 283, .occ 861, .occ 1146, .occ 1147, .occ 1160, .occ 1168, .occ 1191, .occ 1206, .occ 1215, .occ 1238, .occ 1254, .occ 1307, .occ 1368, .occ 1398, .occ 1416, .occ 1436, .occ 1462, .occ 1496, .occ 1518, .occ 1567, .occ 1590, .occ 1618, .sumGe, .nonneg 15, .nonneg 16, .nonneg 20, .nonneg 23, .nonneg 24, .branchGe 2 (1), .branchLe 7 (0), .branchGe 26 (1), .branchLe 14 (0), .branchGe 1 (1), .branchLe 30 (0), .branchGe 17 (1)]

def plane484GenLeaf0329Mult : Fin 42 → Nat := ![72, 598, 288, 324, 2126, 2126, 1900, 326, 204, 715, 188, 14, 110, 265, 571, 383, 241, 18, 1, 355, 421, 110, 188, 305, 747, 14, 251, 543, 102, 2126, 1114, 516, 5352, 1650, 688, 3376, 880, 7910, 920, 2404, 2112, 7010]

theorem plane484GenLeaf0329 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0329Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0329Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0329Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0329Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 125
  · exact hroot.hOcc 137
  · exact hroot.hOcc 140
  · exact hroot.hOcc 141
  · exact hroot.hOcc 283
  · exact hroot.hOcc 861
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1238
  · exact hroot.hOcc 1254
  · exact hroot.hOcc 1307
  · exact hroot.hOcc 1368
  · exact hroot.hOcc 1398
  · exact hroot.hOcc 1416
  · exact hroot.hOcc 1436
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1518
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1618
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17

end QiushiMatmul
