import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0385Refs : Fin 44 → RowRef 1665 43 := ![.occ 122, .occ 123, .occ 132, .occ 133, .occ 134, .occ 137, .occ 138, .occ 180, .occ 330, .occ 446, .occ 447, .occ 498, .occ 594, .occ 627, .occ 641, .occ 835, .occ 1143, .occ 1146, .occ 1166, .occ 1173, .occ 1179, .occ 1196, .occ 1205, .occ 1220, .occ 1221, .occ 1222, .occ 1224, .occ 1246, .occ 1264, .occ 1357, .occ 1488, .occ 1573, .occ 1650, .sumGe, .nonneg 9, .nonneg 26, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchGe 23 (1), .branchGe 35 (1), .branchGe 30 (1), .branchLe 42 (0), .branchGe 8 (1)]

def plane484GenLeaf0385Mult : Fin 44 → Nat := ![396, 1086, 1, 414, 346, 793, 475, 916, 377, 446, 694, 168, 48, 224, 96, 1320, 54, 494, 490, 270, 112, 50, 708, 382, 328, 132, 206, 282, 948, 726, 166, 328, 270, 2246, 648, 114, 272, 2116, 1706, 5338, 3492, 2592, 2080, 6358]

theorem plane484GenLeaf0385 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0385Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0385Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0385Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0385Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 132
  · exact hroot.hOcc 133
  · exact hroot.hOcc 134
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 180
  · exact hroot.hOcc 330
  · exact hroot.hOcc 446
  · exact hroot.hOcc 447
  · exact hroot.hOcc 498
  · exact hroot.hOcc 594
  · exact hroot.hOcc 627
  · exact hroot.hOcc 641
  · exact hroot.hOcc 835
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1221
  · exact hroot.hOcc 1222
  · exact hroot.hOcc 1224
  · exact hroot.hOcc 1246
  · exact hroot.hOcc 1264
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1650
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (9 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8

end QiushiMatmul
