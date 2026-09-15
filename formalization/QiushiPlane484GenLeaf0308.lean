import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0308Refs : Fin 44 → RowRef 1665 43 := ![.occ 85, .occ 122, .occ 136, .occ 187, .occ 206, .occ 261, .occ 350, .occ 662, .occ 672, .occ 1136, .occ 1145, .occ 1151, .occ 1159, .occ 1173, .occ 1187, .occ 1188, .occ 1190, .occ 1191, .occ 1208, .occ 1216, .occ 1262, .occ 1315, .occ 1325, .occ 1353, .occ 1471, .occ 1567, .occ 1571, .occ 1597, .occ 1624, .occ 1650, .occ 1652, .sumGe, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchGe 29 (1), .branchGe 34 (1), .branchGe 36 (1), .branchLe 42 (0), .branchGe 30 (1), .branchLe 12 (0), .branchLe 20 (0)]

def plane484GenLeaf0308Mult : Fin 44 → Nat := ![5261, 10230, 6725, 20550, 24412, 2278, 6263, 2745, 9797, 6831, 10873, 1037, 8724, 2648, 5867, 10420, 7635, 880, 3793, 9025, 5208, 570, 1972, 5569, 658, 2752, 6780, 7992, 7008, 2860, 7974, 39805, 12687, 12127, 20252, 24823, 27920, 62563, 85662, 86815, 39147, 50271, 25721, 39805]

theorem plane484GenLeaf0308 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0308Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0308Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0308Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0308Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 85
  · exact hroot.hOcc 122
  · exact hroot.hOcc 136
  · exact hroot.hOcc 187
  · exact hroot.hOcc 206
  · exact hroot.hOcc 261
  · exact hroot.hOcc 350
  · exact hroot.hOcc 662
  · exact hroot.hOcc 672
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1262
  · exact hroot.hOcc 1315
  · exact hroot.hOcc 1325
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1624
  · exact hroot.hOcc 1650
  · exact hroot.hOcc 1652
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (36 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (12 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20

end QiushiMatmul
