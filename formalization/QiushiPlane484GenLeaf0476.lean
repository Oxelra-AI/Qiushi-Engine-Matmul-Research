import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0476Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 125, .occ 130, .occ 133, .occ 135, .occ 142, .occ 170, .occ 356, .occ 615, .occ 674, .occ 691, .occ 1150, .occ 1172, .occ 1183, .occ 1246, .occ 1248, .occ 1339, .occ 1358, .occ 1371, .occ 1431, .occ 1437, .occ 1446, .occ 1471, .occ 1483, .occ 1484, .occ 1523, .occ 1590, .occ 1603, .occ 1639, .sumGe, .nonneg 16, .nonneg 17, .nonneg 22, .nonneg 25, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchGe 0 (1), .branchLe 19 (0), .branchLe 3 (0), .branchGe 38 (1), .branchLe 34 (0), .branchLe 6 (0), .branchGe 21 (1)]

def plane484GenLeaf0476Mult : Fin 44 → Nat := ![4083, 1353, 223, 6876, 4641, 10381, 1104, 3266, 631, 2196, 2032, 151, 4215, 2681, 1343, 9, 3059, 602, 355, 629, 2375, 1059, 1353, 751, 955, 1531, 2335, 3238, 334, 10715, 1955, 2335, 7750, 13226, 26260, 9009, 4640, 12658, 3688, 9261, 16970, 10715, 6481, 33000]

theorem plane484GenLeaf0476 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0476Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0476Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0476Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0476Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 125
  · exact hroot.hOcc 130
  · exact hroot.hOcc 133
  · exact hroot.hOcc 135
  · exact hroot.hOcc 142
  · exact hroot.hOcc 170
  · exact hroot.hOcc 356
  · exact hroot.hOcc 615
  · exact hroot.hOcc 674
  · exact hroot.hOcc 691
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1246
  · exact hroot.hOcc 1248
  · exact hroot.hOcc 1339
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1371
  · exact hroot.hOcc 1431
  · exact hroot.hOcc 1437
  · exact hroot.hOcc 1446
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1523
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1639
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (38 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21

end QiushiMatmul
