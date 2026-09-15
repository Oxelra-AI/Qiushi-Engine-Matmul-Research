import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0255Refs : Fin 44 → RowRef 1665 43 := ![.occ 122, .occ 124, .occ 125, .occ 136, .occ 179, .occ 194, .occ 341, .occ 355, .occ 426, .occ 615, .occ 834, .occ 1136, .occ 1150, .occ 1170, .occ 1186, .occ 1191, .occ 1206, .occ 1358, .occ 1435, .occ 1437, .occ 1449, .occ 1470, .occ 1478, .occ 1481, .occ 1546, .occ 1606, .occ 1609, .occ 1610, .occ 1661, .sumGe, .nonneg 8, .nonneg 22, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchLe 29 (0), .branchGe 17 (1), .branchLe 3 (0), .branchLe 20 (0), .branchLe 13 (0), .branchLe 25 (0), .branchGe 4 (1)]

def plane484GenLeaf0255Mult : Fin 44 → Nat := ![740, 944, 2249, 1911, 996, 1540, 1507, 199, 717, 1432, 137, 613, 1104, 419, 408, 1079, 762, 172, 505, 447, 146, 392, 353, 793, 909, 248, 299, 855, 309, 4347, 350, 66, 3413, 3037, 1498, 1303, 4347, 2941, 7826, 3253, 3575, 323, 1931, 9103]

theorem plane484GenLeaf0255 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0255Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0255Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0255Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0255Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 122
  · exact hroot.hOcc 124
  · exact hroot.hOcc 125
  · exact hroot.hOcc 136
  · exact hroot.hOcc 179
  · exact hroot.hOcc 194
  · exact hroot.hOcc 341
  · exact hroot.hOcc 355
  · exact hroot.hOcc 426
  · exact hroot.hOcc 615
  · exact hroot.hOcc 834
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1435
  · exact hroot.hOcc 1437
  · exact hroot.hOcc 1449
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1546
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1661
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
