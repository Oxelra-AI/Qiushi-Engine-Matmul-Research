import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0326Refs : Fin 44 → RowRef 1665 43 := ![.occ 88, .occ 119, .occ 123, .occ 128, .occ 137, .occ 139, .occ 141, .occ 251, .occ 270, .occ 276, .occ 861, .occ 1124, .occ 1143, .occ 1145, .occ 1146, .occ 1151, .occ 1168, .occ 1215, .occ 1216, .occ 1303, .occ 1376, .occ 1392, .occ 1398, .occ 1462, .occ 1489, .occ 1496, .occ 1602, .occ 1610, .occ 1628, .sumGe, .nonneg 23, .nonneg 24, .nonneg 25, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchGe 26 (1), .branchLe 14 (0), .branchGe 1 (1), .branchLe 30 (0), .branchLe 17 (0), .branchGe 38 (1), .branchLe 16 (0), .branchLe 22 (0)]

def plane484GenLeaf0326Mult : Fin 44 → Nat := ![60, 639, 506, 104, 1584, 1288, 1122, 720, 204, 168, 953, 667, 721, 264, 1181, 22, 784, 1640, 937, 238, 346, 667, 307, 211, 645, 1153, 94, 116, 213, 3752, 166, 585, 76, 3514, 2302, 2554, 8123, 2676, 1346, 3752, 623, 5136, 667, 3514]

theorem plane484GenLeaf0326 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0326Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0326Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0326Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0326Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 88
  · exact hroot.hOcc 119
  · exact hroot.hOcc 123
  · exact hroot.hOcc 128
  · exact hroot.hOcc 137
  · exact hroot.hOcc 139
  · exact hroot.hOcc 141
  · exact hroot.hOcc 251
  · exact hroot.hOcc 270
  · exact hroot.hOcc 276
  · exact hroot.hOcc 861
  · exact hroot.hOcc 1124
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1303
  · exact hroot.hOcc 1376
  · exact hroot.hOcc 1392
  · exact hroot.hOcc 1398
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1628
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (38 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22

end QiushiMatmul
