import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0083Refs : Fin 42 → RowRef 1665 43 := ![.occ 121, .occ 123, .occ 130, .occ 134, .occ 544, .occ 764, .occ 765, .occ 766, .occ 958, .occ 1036, .occ 1173, .occ 1252, .occ 1316, .occ 1318, .occ 1319, .occ 1320, .occ 1367, .occ 1374, .occ 1395, .occ 1413, .occ 1414, .occ 1416, .occ 1457, .occ 1468, .occ 1488, .occ 1489, .occ 1607, .occ 1638, .occ 1644, .occ 1661, .sumGe, .nonneg 0, .nonneg 3, .nonneg 4, .nonneg 5, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchGe 13 (1), .branchGe 42 (1), .branchGe 9 (1), .branchLe 37 (0)]

def plane484GenLeaf0083Mult : Fin 42 → Nat := ![991, 614, 967, 62, 145, 671, 55, 481, 186, 89, 34, 56, 55, 72, 154, 144, 273, 65, 626, 56, 561, 341, 34, 199, 101, 472, 31, 22, 46, 263, 1286, 9, 3164, 22, 65, 1214, 31, 1185, 3464, 3054, 6153, 814]

theorem plane484GenLeaf0083 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0083Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0083Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0083Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0083Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 123
  · exact hroot.hOcc 130
  · exact hroot.hOcc 134
  · exact hroot.hOcc 544
  · exact hroot.hOcc 764
  · exact hroot.hOcc 765
  · exact hroot.hOcc 766
  · exact hroot.hOcc 958
  · exact hroot.hOcc 1036
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1252
  · exact hroot.hOcc 1316
  · exact hroot.hOcc 1318
  · exact hroot.hOcc 1319
  · exact hroot.hOcc 1320
  · exact hroot.hOcc 1367
  · exact hroot.hOcc 1374
  · exact hroot.hOcc 1395
  · exact hroot.hOcc 1413
  · exact hroot.hOcc 1414
  · exact hroot.hOcc 1416
  · exact hroot.hOcc 1457
  · exact hroot.hOcc 1468
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1638
  · exact hroot.hOcc 1644
  · exact hroot.hOcc 1661
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (9 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9
  · change (∑ k, (if k = (37 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37

end QiushiMatmul
