import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0088Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 125, .occ 130, .occ 131, .occ 133, .occ 134, .occ 194, .occ 429, .occ 812, .occ 1150, .occ 1170, .occ 1172, .occ 1186, .occ 1220, .occ 1237, .occ 1243, .occ 1257, .occ 1340, .occ 1442, .occ 1444, .occ 1448, .occ 1450, .occ 1472, .occ 1478, .occ 1518, .occ 1539, .occ 1546, .occ 1554, .occ 1597, .occ 1602, .occ 1635, .occ 1639, .sumGe, .nonneg 12, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchGe 4 (1), .branchLe 36 (0), .branchLe 26 (0), .branchLe 24 (0), .branchGe 19 (1), .branchLe 6 (0), .branchLe 18 (0)]

def plane484GenLeaf0088Mult : Fin 44 → Nat := ![3031, 2240, 5781, 700, 2402, 644, 2088, 5120, 10, 2158, 487, 117, 730, 520, 1044, 1947, 143, 1214, 927, 316, 317, 526, 1044, 3906, 937, 78, 2233, 298, 520, 38, 3590, 986, 10674, 864, 6358, 3128, 10674, 25624, 9110, 9688, 6384, 8098, 4610, 9714]

theorem plane484GenLeaf0088 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0088Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0088Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0088Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0088Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 125
  · exact hroot.hOcc 130
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 134
  · exact hroot.hOcc 194
  · exact hroot.hOcc 429
  · exact hroot.hOcc 812
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1237
  · exact hroot.hOcc 1243
  · exact hroot.hOcc 1257
  · exact hroot.hOcc 1340
  · exact hroot.hOcc 1442
  · exact hroot.hOcc 1444
  · exact hroot.hOcc 1448
  · exact hroot.hOcc 1450
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1518
  · exact hroot.hOcc 1539
  · exact hroot.hOcc 1546
  · exact hroot.hOcc 1554
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1635
  · exact hroot.hOcc 1639
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (12 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18

end QiushiMatmul
