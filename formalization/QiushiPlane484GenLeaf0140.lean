import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0140Refs : Fin 43 → RowRef 1665 43 := ![.occ 130, .occ 133, .occ 134, .occ 139, .occ 145, .occ 179, .occ 187, .occ 618, .occ 681, .occ 817, .occ 861, .occ 1140, .occ 1151, .occ 1161, .occ 1168, .occ 1170, .occ 1172, .occ 1179, .occ 1215, .occ 1216, .occ 1228, .occ 1257, .occ 1261, .occ 1462, .occ 1471, .occ 1543, .occ 1609, .occ 1629, .occ 1649, .occ 1652, .sumGe, .nonneg 5, .nonneg 22, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 39 (0), .branchGe 32 (1), .branchGe 37 (1), .branchGe 1 (1), .branchGe 38 (1)]

def plane484GenLeaf0140Mult : Fin 43 → Nat := ![401, 1150, 224, 416, 279, 619, 1662, 1476, 310, 454, 797, 2496, 744, 530, 292, 642, 316, 492, 1122, 442, 508, 38, 204, 1652, 1010, 342, 1022, 240, 214, 528, 3924, 76, 706, 2006, 3924, 6860, 2576, 2988, 242, 8676, 3392, 7780, 7354]

theorem plane484GenLeaf0140 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0140Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0140Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0140Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0140Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 130
  · exact hroot.hOcc 133
  · exact hroot.hOcc 134
  · exact hroot.hOcc 139
  · exact hroot.hOcc 145
  · exact hroot.hOcc 179
  · exact hroot.hOcc 187
  · exact hroot.hOcc 618
  · exact hroot.hOcc 681
  · exact hroot.hOcc 817
  · exact hroot.hOcc 861
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1161
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1228
  · exact hroot.hOcc 1257
  · exact hroot.hOcc 1261
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1543
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1629
  · exact hroot.hOcc 1649
  · exact hroot.hOcc 1652
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (32 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (38 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38

end QiushiMatmul
