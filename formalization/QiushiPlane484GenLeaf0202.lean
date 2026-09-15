import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0202Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 121, .occ 129, .occ 139, .occ 148, .occ 216, .occ 220, .occ 358, .occ 437, .occ 470, .occ 581, .occ 751, .occ 828, .occ 1133, .occ 1140, .occ 1150, .occ 1151, .occ 1154, .occ 1214, .occ 1227, .occ 1235, .occ 1324, .occ 1341, .occ 1371, .occ 1443, .occ 1472, .occ 1478, .occ 1597, .occ 1601, .occ 1603, .occ 1608, .occ 1622, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchGe 35 (1), .branchLe 16 (0), .branchLe 18 (0), .branchGe 1 (1), .branchLe 22 (0), .branchGe 21 (1), .branchGe 31 (1), .branchLe 10 (0)]

def plane484GenLeaf0202Mult : Fin 44 → Nat := ![6934, 3618, 351, 2526, 5760, 6825, 17028, 6243, 15647, 24968, 1640, 1493, 16950, 8760, 2140, 5173, 11998, 5858, 9696, 15793, 1370, 15348, 13759, 3761, 248, 4165, 2474, 1692, 5886, 14698, 7475, 4856, 40200, 4465, 40200, 154871, 80607, 32818, 37674, 19540, 8534, 90284, 100626, 40200]

theorem plane484GenLeaf0202 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0202Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0202Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0202Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0202Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 129
  · exact hroot.hOcc 139
  · exact hroot.hOcc 148
  · exact hroot.hOcc 216
  · exact hroot.hOcc 220
  · exact hroot.hOcc 358
  · exact hroot.hOcc 437
  · exact hroot.hOcc 470
  · exact hroot.hOcc 581
  · exact hroot.hOcc 751
  · exact hroot.hOcc 828
  · exact hroot.hOcc 1133
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1227
  · exact hroot.hOcc 1235
  · exact hroot.hOcc 1324
  · exact hroot.hOcc 1341
  · exact hroot.hOcc 1371
  · exact hroot.hOcc 1443
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1622
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10

end QiushiMatmul
