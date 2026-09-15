import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0044Refs : Fin 41 → RowRef 1665 43 := ![.occ 120, .occ 136, .occ 137, .occ 177, .occ 586, .occ 587, .occ 749, .occ 776, .occ 1190, .occ 1205, .occ 1206, .occ 1221, .occ 1231, .occ 1309, .occ 1313, .occ 1314, .occ 1327, .occ 1357, .occ 1388, .occ 1398, .occ 1428, .occ 1433, .occ 1470, .occ 1524, .occ 1552, .occ 1553, .sumGe, .nonneg 2, .nonneg 23, .nonneg 25, .branchLe 15 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchGe 17 (1), .branchLe 7 (0), .branchLe 18 (0), .branchLe 1 (0), .branchLe 5 (0), .branchGe 16 (1), .branchGe 10 (1)]

def plane484GenLeaf0044Mult : Fin 41 → Nat := ![526, 386, 482, 399, 257, 53, 4, 142, 30, 31, 121, 52, 96, 168, 8, 142, 20, 124, 44, 104, 18, 24, 314, 46, 26, 116, 650, 248, 124, 124, 498, 650, 650, 620, 1569, 650, 336, 184, 34, 1112, 1997]

theorem plane484GenLeaf0044 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0044Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0044Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0044Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0044Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 177
  · exact hroot.hOcc 586
  · exact hroot.hOcc 587
  · exact hroot.hOcc 749
  · exact hroot.hOcc 776
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1221
  · exact hroot.hOcc 1231
  · exact hroot.hOcc 1309
  · exact hroot.hOcc 1313
  · exact hroot.hOcc 1314
  · exact hroot.hOcc 1327
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1388
  · exact hroot.hOcc 1398
  · exact hroot.hOcc 1428
  · exact hroot.hOcc 1433
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1524
  · exact hroot.hOcc 1552
  · exact hroot.hOcc 1553
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
