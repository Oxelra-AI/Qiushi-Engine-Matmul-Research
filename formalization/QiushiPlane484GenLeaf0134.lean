import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0134Refs : Fin 43 → RowRef 1665 43 := ![.occ 119, .occ 121, .occ 123, .occ 128, .occ 132, .occ 134, .occ 139, .occ 148, .occ 149, .occ 195, .occ 363, .occ 402, .occ 861, .occ 1113, .occ 1215, .occ 1255, .occ 1273, .occ 1309, .occ 1316, .occ 1381, .occ 1428, .occ 1432, .occ 1477, .occ 1491, .occ 1529, .occ 1557, .occ 1615, .occ 1623, .occ 1629, .occ 1630, .occ 1660, .sumGe, .nonneg 9, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 39 (0), .branchGe 32 (1), .branchLe 37 (0), .branchGe 3 (1), .branchLe 38 (0)]

def plane484GenLeaf0134Mult : Fin 43 → Nat := ![12142, 9354, 879, 2162, 11054, 7602, 3152, 19719, 12059, 4590, 1690, 15594, 4478, 468, 2608, 108, 9064, 12044, 4021, 4104, 3620, 457, 1641, 7675, 485, 14763, 1763, 3155, 5822, 3500, 11737, 40319, 903, 17040, 31765, 68264, 37164, 6119, 40319, 72256, 38556, 55000, 37711]

theorem plane484GenLeaf0134 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0134Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0134Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0134Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0134Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 123
  · exact hroot.hOcc 128
  · exact hroot.hOcc 132
  · exact hroot.hOcc 134
  · exact hroot.hOcc 139
  · exact hroot.hOcc 148
  · exact hroot.hOcc 149
  · exact hroot.hOcc 195
  · exact hroot.hOcc 363
  · exact hroot.hOcc 402
  · exact hroot.hOcc 861
  · exact hroot.hOcc 1113
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1255
  · exact hroot.hOcc 1273
  · exact hroot.hOcc 1309
  · exact hroot.hOcc 1316
  · exact hroot.hOcc 1381
  · exact hroot.hOcc 1428
  · exact hroot.hOcc 1432
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1529
  · exact hroot.hOcc 1557
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1623
  · exact hroot.hOcc 1629
  · exact hroot.hOcc 1630
  · exact hroot.hOcc 1660
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (9 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (32 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32
  · change (∑ k, (if k = (37 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3
  · change (∑ k, (if k = (38 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38

end QiushiMatmul
