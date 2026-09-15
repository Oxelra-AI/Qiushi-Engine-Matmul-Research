import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0154Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 121, .occ 127, .occ 128, .occ 134, .occ 136, .occ 138, .occ 141, .occ 143, .occ 233, .occ 401, .occ 406, .occ 592, .occ 1010, .occ 1025, .occ 1164, .occ 1166, .occ 1215, .occ 1216, .occ 1251, .occ 1258, .occ 1273, .occ 1283, .occ 1321, .occ 1352, .occ 1511, .occ 1519, .occ 1526, .occ 1542, .occ 1642, .occ 1655, .sumGe, .nonneg 0, .nonneg 11, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchGe 7 (1), .branchLe 18 (0), .branchLe 30 (0), .branchLe 21 (0), .branchLe 42 (0), .branchGe 26 (1)]

def plane484GenLeaf0154Mult : Fin 44 → Nat := ![5030, 3420, 2249, 1158, 1512, 2965, 2183, 286, 583, 7845, 1114, 422, 101, 530, 105, 1836, 1238, 2266, 3467, 943, 1777, 4202, 2286, 414, 237, 1138, 1100, 640, 598, 2168, 383, 10988, 869, 4532, 6637, 3089, 10946, 10988, 21028, 4351, 8820, 10988, 10988, 16108]

theorem plane484GenLeaf0154 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0154Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0154Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0154Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0154Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 127
  · exact hroot.hOcc 128
  · exact hroot.hOcc 134
  · exact hroot.hOcc 136
  · exact hroot.hOcc 138
  · exact hroot.hOcc 141
  · exact hroot.hOcc 143
  · exact hroot.hOcc 233
  · exact hroot.hOcc 401
  · exact hroot.hOcc 406
  · exact hroot.hOcc 592
  · exact hroot.hOcc 1010
  · exact hroot.hOcc 1025
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1251
  · exact hroot.hOcc 1258
  · exact hroot.hOcc 1273
  · exact hroot.hOcc 1283
  · exact hroot.hOcc 1321
  · exact hroot.hOcc 1352
  · exact hroot.hOcc 1511
  · exact hroot.hOcc 1519
  · exact hroot.hOcc 1526
  · exact hroot.hOcc 1542
  · exact hroot.hOcc 1642
  · exact hroot.hOcc 1655
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (21 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26

end QiushiMatmul
